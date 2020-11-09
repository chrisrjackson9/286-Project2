#include <iostream>
#include <fstream>
#include <unistd.h>
#include <fcntl.h>
#include <iomanip>
#include <bitset>
#include <sstream>
using namespace std;

string SIM_INSTR[1000];
int writeBack[1000];
string DECODE[1000];
int SIM_DATA[1000];
bitset<32> bit[1000];
int missList[2];
int REGISTERS[32];
int instructionDest[1000];
int instructionSrc1[1000];
int instructionSrc2[1000];
int bufferDest[10];
int bufferSrc1[10];
int bufferSrc2[10];
int execute[10];
string preissue[4] = {"", "", "", ""};
string prealu[2] = {"", ""};
string postalu[1] = {""};
string premem[2] = {"", ""};
string postmem[2] = {"", ""};
int addr = 96;
int dataStart = 0;
int out[4][2][3] = {
    {{0, 0, 0}, {0, 0, 0}},
    {{0, 0, 0}, {0, 0, 0}},
    {{0, 0, 0}, {0, 0, 0}},
    {{0, 0, 0}, {0, 0, 0}}};

bitset<32> outBin[4][2][2] = {
    {{0, 0}, {0, 0}},
    {{0, 0}, {0, 0}},
    {{0, 0}, {0, 0}},
    {{0, 0}, {0, 0}}};

int LRU[4] = {0, 0, 0, 0};
int memCount = 0;
string branches[10];

void sim(ofstream &ofs);
bool isFileOpenForOutput(ofstream &ofs, const string &filename);

void printCache(ofstream &ofs);
bool accessCache(ofstream &ofs, int addr, int wData);
void missListUpdate(ofstream &ofs, int address);

void add(int rd, int rs, int rt);
void sub(int rd, int rs, int rt);
void mul(int rd, int rs, int rt);
void addi(int rt, int rs, int immediate);
void sw(int rt, int offset, int base);
void sh(int rt, int offset, int base);
void lw(int rt, int offset, int base);
void movz(int rd, int rs, int rt);
void OR(int rd, int rs, int rt);
void AND(int rd, int rs, int rt);
void beq(int rs, int rt, int offset, int &i);
void bltz(int rs, int offset, int &i);
void sll(int rd, int rt, int sa);
void srl(int rd, int rt, int sa);
void jr(int rs, int &i);
void j(int target, int &i);

void fetch(ofstream &ofs, int &address);
void issue(int address);
void alu();
void mem(ofstream &ofs);
void wb(ofstream &ofs);
bool isBranch(int address);
bool hazardChecking(int compare);
void executeBranch(int &address);

int main(int argc, char **argv)
{
    string ofile;
    ofstream assembly;
    ofstream simulator;
    ostringstream oss;
    ostringstream result;
    ostringstream simple;
    string binSpace;
    string text;
    string stext;
    string disFile = "";
    string simFile = "";
    int type = 1;
    int breakCheck = 0;

    for (int i = 0; i < 10; i++)
    {
        bufferDest[i] = -1;
        bufferSrc1[i] = -1;
        bufferSrc2[i] = -1;
    }

    for (int i = 0; i < 32; i++)
    {
        REGISTERS[i] = 0;
    }

    char buffer[4];
    int i;
    char *iPtr;
    iPtr = (char *)(void *)&i;

    int FD;

    if (argc >= 2)
    {
        FD = open(argv[2], O_RDONLY);
        ofile = argv[4];
        disFile = ofile + "_dis.txt";
        simFile = ofile + "_sim.txt";
        isFileOpenForOutput(assembly, disFile);
        isFileOpenForOutput(simulator, simFile);
    }
    else
    {
        FD = open("test1.bin", O_RDONLY);
        isFileOpenForOutput(assembly, "testDis.txt");
        isFileOpenForOutput(simulator, "testSim.txt");
    }

    int amt = 4;

    while (amt != 0)
    {
        amt = read(FD, buffer, 4);
        if (amt == 4)
        {
            iPtr[0] = buffer[3];
            iPtr[1] = buffer[2];
            iPtr[2] = buffer[1];
            iPtr[3] = buffer[0];

            //store bits into x
            bitset<32> x(i);
            bit[addr] = i;

            if (text.compare("BREAK") != 0)
            {
                //put x into a string stream
                oss << x;
                //convert oss into string
                binSpace = oss.str();
                //clear stream
                oss.str("");
                //insert spaces into instruction
                binSpace.insert(1, " ");
                binSpace.insert(7, " ");
                binSpace.insert(13, " ");
                binSpace.insert(19, " ");
                binSpace.insert(25, " ");
                binSpace.insert(31, " ");

                //decode instruction
                int valid = i >> 31;
                int nop = (((unsigned int)i) << 1);
                int opcode = (((unsigned int)i) >> 26);
                int final = ((((unsigned int)i) << 26) >> 26);
                int immediate = ((((signed int)i) << 16) >> 16);
                int rs = ((((unsigned int)i) << 6) >> 27);
                int rt = ((((unsigned int)i) << 11) >> 27);
                int rd = ((((unsigned int)i) << 16) >> 27);
                int sa = ((((unsigned int)i) << 21) >> 27);
                int instr_index = (4 * ((((unsigned int)i) << 6) >> 6));

                //analyze opcode
                if (nop == 0)
                {
                    simple << "NOP";
                }
                if (valid == 0)
                {
                    result << "Invalid Instruction";
                }

                switch (opcode)
                {
                case 32:
                    switch (final)
                    {
                    case 8:
                        result << "JR\tR" << rs;
                        simple << "JR " << rs;
                        break;
                    case 34:
                        instructionDest[addr] = rd;
                        instructionSrc1[addr] = rs;
                        instructionSrc2[addr] = rt;
                        result << "SUB\t"
                               << "R" << rd << ", R" << rs << ", R" << rt;
                        simple << "SUB " << rd << " " << rs << " " << rt;
                        break;
                    case 37:
                        instructionDest[addr] = rd;
                        instructionSrc1[addr] = rs;
                        instructionSrc2[addr] = rt;
                        result << "OR\t"
                               << "R" << rd << ", R" << rs << ", R" << rt;
                        simple << "OR " << rd << " " << rs << " " << rt;
                        break;
                    case 10:
                        instructionDest[addr] = rd;
                        instructionSrc1[addr] = rs;
                        instructionSrc2[addr] = rt;
                        result << "MOVZ\t"
                               << "R" << rd << ", R" << rs << ", R" << rt;
                        simple << "MOVZ " << rd << " " << rs << " " << rt;
                        break;
                    case 36:
                        instructionDest[addr] = rd;
                        instructionSrc1[addr] = rs;
                        instructionSrc2[addr] = rt;
                        result << "AND\t"
                               << "R" << rd << ", R" << rs << ", R" << rt;
                        simple << "AND " << rd << " " << rs << " " << rt;
                        break;
                    case 32:
                        instructionDest[addr] = rd;
                        instructionSrc1[addr] = rs;
                        instructionSrc2[addr] = rt;
                        result << "ADD\t"
                               << "R" << rd << ", R" << rs << ", R" << rt;
                        simple << "ADD " << rd << " " << rs << " " << rt;
                        break;
                    case 0:
                        if (rt != 0 || rd != 0 || sa != 0)
                        {
                            result << "SLL\t"
                                   << "R" << rd << ", R" << rt << ", #" << sa;
                            simple << "SLL " << rd << " " << rt << " " << sa;
                        }
                        break;
                    case 2:
                        result << "SRL\t"
                               << "R" << rd << ", R" << rt << ", #" << sa;
                        simple << "SRL " << rd << " " << rt << " " << sa;
                        break;
                    case 13:
                        result << "BREAK";
                        simple << "BREAK";
                        break;
                    default:
                        break;
                    }
                    break;
                case 60:
                    instructionDest[addr] = rd;
                    instructionSrc1[addr] = rs;
                    instructionSrc2[addr] = rt;
                    result << "MUL\t"
                           << "R" << rd << ", R" << rs << ", R" << rt;
                    simple << "MUL " << rd << " " << rs << " " << rt;
                    break;
                case 33:
                    instructionSrc1[addr] = rs;
                    result << "BLTZ\t"
                           << "R" << rs << ", #" << immediate * 4;
                    simple << "BLTZ " << rs << " " << immediate * 4;
                    break;
                case 40:
                    instructionDest[addr] = rt;
                    instructionSrc1[addr] = rs;
                    result << "ADDI\t"
                           << "R" << rt << ", R" << rs << ", #" << immediate;
                    simple << "ADDI " << rt << " " << rs << " " << immediate;
                    break;
                case 43:
                    instructionDest[addr] = rt;
                    instructionSrc1[addr] = rs;
                    result << "SW\t"
                           << "R" << rt << ", " << immediate << "(R" << rs << ")";
                    simple << "SW " << rt << " " << immediate << " " << rs;
                    break;
                case 36:
                    instructionSrc1[addr] = rs;
                    instructionSrc2[addr] = rt;
                    result << "BEQ\t"
                           << "R" << rs << ", R" << rt << ", #" << immediate;
                    simple << "BEQ " << rs << " " << rt << " " << immediate;
                    break;
                case 34:

                    result << "J\t#" << instr_index;
                    simple << "J " << instr_index;
                    break;
                case 35:
                    instructionDest[addr] = rt;
                    instructionSrc1[addr] = rs;
                    result << "LW\t"
                           << "R" << rt << ", " << immediate << "(R" << rs << ")";
                    simple << "LW " << rt << " " << immediate << " " << rs;
                    break;
                case 73:
                    instructionDest[addr] = rs;
                    instructionSrc1[addr] = rt;
                    result << "SH\t"
                           << "R" << rt << ", " << immediate << ", (R" << rs << ")";
                    simple << "SH " << rt << " " << immediate << " " << rs;
                    break;
                default:
                    text = "";
                    stext = "";
                    break;
                }

                //Put results into text
                text = result.str();
                stext = simple.str();
                //Put instruction into array
                SIM_INSTR[addr] = text;
                DECODE[addr] = stext;
                //Clear stream
                result.str("");
                simple.str("");
                //Output results before BREAK Instruction
                assembly << binSpace << " " << addr << " " << text << endl;
            } //end of if (text.comapare("BREAK") != 0)
            else
            {
                if (text.compare("BREAK") != 0 && breakCheck == 0)
                {
                    SIM_INSTR[addr] = "BREAK";
                    breakCheck = 1;
                }
                //find first line after
                if (dataStart == 0)
                {
                    dataStart = addr;
                }
                //Put data into array
                SIM_DATA[addr] = i;
                bit[addr] = x;
                //Output results after BREAK Instruction
                assembly << x << "\t" << addr << " " << i << endl;
            }
            addr += amt;
        } //end of if (amt ==4)
    }     //end of while (amt != 0)
    sim(simulator);
    assembly.close();
    return 0;
} //end of main

bool isFileOpenForOutput(ofstream &ofs, const string &filename)
{
    //Attempt to open file
    ofs.open(filename);
    //check if file is open
    if (!ofs.is_open())
    {
        return false;
    }
    else
    {
        return true;
    }
}

void sim(ofstream &ofs)
{
    int cycleNum = 1;
    int mod;
    int rd, rt, rs, sa, immediate;
    int wData;
    bool done = true;
    bool writeBack = false;
    string instruction;
    istringstream iss;

    for (int i = 0; i < 1000; i += 4)
    {
        if (SIM_INSTR[i].size() != 0 || branches[0].size() != 0 || !done)
        {
            done = true;

            for (int i = 0; i < 4; i++)
            {
                if (preissue[i].size() != 0)
                {
                    done = false;
                }
            }

            for (int i = 0; i < 2; i++)
            {
                if (prealu[i].size() != 0 || premem[i].size() != 0)
                {
                    done = false;
                }
            }

            if (postalu[0].size() != 0 or postmem[0].size() != 0)
            {
                done = false;
            }

            missListUpdate(ofs, i);

            ofs << "--------------------" << endl;
            ofs << "Cycle: " << cycleNum << "\t" << endl
                << endl;
            ofs << "Pre-Issue Buffer: " << endl
                << "\tEntry 0:" << preissue[0] << endl // << "Src1 " << bufferSrc1[0] << " Src2 " << bufferSrc2[0] << " Dest " << bufferDest[0]// << endl
                << "\tEntry 1:" << preissue[1] << endl // << "Src1 " << bufferSrc1[1] << " Src2 " << bufferSrc2[1] << " Dest " << bufferDest[1] << endl
                << "\tEntry 2:" << preissue[2] << endl // << "Src1 " << bufferSrc1[2] << " Src2 " << bufferSrc2[2] << " Dest " << bufferDest[2] << endl
                << "\tEntry 3:" << preissue[3] << endl // << "Src1 " << bufferSrc1[3] << " Src2 " << bufferSrc2[3] << " Dest " << bufferDest[3] << endl
                << "Pre_ALU Queue:" << endl
                << "\tEntry 0:" << prealu[0] << endl // << "Src1 " << bufferSrc1[4] << " Src2 " << bufferSrc2[4] << " Dest " << bufferDest[4] << endl
                << "\tEntry 1:" << prealu[1] << endl // << "Src1 " << bufferSrc1[5] << " Src2 " << bufferSrc2[5] << " Dest " << bufferDest[5] << endl
                << "Post_ALU Queue:" << endl
                << "\tEntry 0:" << postalu[0] << endl // << "Src1 " << bufferSrc1[6] << " Src2 " << bufferSrc2[6] << " Dest " << bufferDest[6] << endl
                << "Pre_MEM Queue:" << endl
                << "\tEntry 0:" << premem[0] << endl // << "Src1 " << bufferSrc1[7] << " Src2 " << bufferSrc2[7] << " Dest " << bufferDest[7] << endl
                << "\tEntry 1:" << premem[1] << endl // << "Src1 " << bufferSrc1[8] << " Src2 " << bufferSrc2[8] << " Dest " << bufferDest[8] << endl
                << "Post_MEM Queue:" << endl
                << "\tEntry 0:" << postmem[0] << endl // << "Src1 " << bufferSrc1[9] << " Src2 " << bufferSrc2[9] << " Dest " << bufferDest[9] << endl
                << endl;

            ofs << "Registers";
            for (int i = 0; i < 32; i++)
            {
                if (i % 8 == 0)
                {
                    ofs << endl
                        << "R" << setw(2) << setfill('0') << i << ": \t" << REGISTERS[i] << "\t";
                }
                else
                    ofs << REGISTERS[i] << "\t ";
            }

            ofs << endl
                << endl;

            printCache(ofs);

            ofs << endl
                << "Data";

            mod = 8;

            for (int j = dataStart; j <= addr - 4; j += 4)
            {
                if (mod % 8 == 0)
                {
                    ofs << endl
                        << j << ": \t" << SIM_DATA[j] << "\t";
                }
                else
                    ofs << SIM_DATA[j] << "\t ";
                mod++;
            }

            wb(ofs);

            alu();
            mem(ofs);
            issue(i);
            fetch(ofs, i);
            executeBranch(i);

            ofs << endl;
            iss.clear();
            cycleNum++;
        }
    }
}

void printCache(ofstream &ofs)
{
    ofs << "Cache" << endl;
    for (int i = 0; i < 4; i++)
    {
        ofs << "Set " << i << ": LRU=" << LRU[i] << endl;
        for (int j = 0; j < 2; j++)
        {
            ofs << "\tEntry " << (j) << ":[(" << out[i][j][0] << "," << out[i][j][1] << "," << out[i][j][2] << ")<"
                << outBin[i][j][0] << "," << outBin[i][j][1] << ">]" << endl;
        }
    }
}

bool accessCache(ofstream &ofs, int address, int data = 0)
{
    int addr = address >> 2;
    int word = addr && 0x00000001;
    addr = addr >> 1;
    int index = addr & 0x00000003;
    int tag = addr >> 2;
    int way = -1;

    if (out[index][0][0] == 1 && out[index][0][2] == tag)
    {
        way = 0;
        LRU[index] = 1;
    }
    else if (out[index][1][0] == 1 && out[index][1][2] == tag)
    {
        way = 1;
        LRU[index] = 0;
    }

    if (!(way == 1 || way == 0))
    {

        if (address < 96)
        {
            missList[0] = address + 4;
            missList[1] = address + 8;
        }
        else if (DECODE[address].compare("BREAK") == 0)
        {
            missList[0] = address - 4;
            missList[1] = address;
        }
        else
        {
            missList[0] = address;
            missList[1] = address + 4;
        }
        return false;
    }
    return true;
}

void missListUpdate(ofstream &ofs, int address)
{
    int addr = address >> 2;
    int word = addr && 0x00000001;
    addr = addr >> 1;
    int index = addr & 0x00000003;
    int tag = addr >> 2;
    int way;
    bool dirty = false;
    bitset<32> valid = bit[address] >> 31;

    if (!(missList[0] == 0 && missList[1] == 0))
    {
        if (LRU[index] == 0)
        {
            outBin[index][0][0] = bit[missList[0]];
            outBin[index][0][1] = bit[missList[1]];
            out[index][0][0] = 1;
            out[index][0][2] = tag;

            if (preissue[0].size() == 0)
            {
                for (int i = 0; i < 2; i++)
                {

                    if (SIM_INSTR[address + (i * 4)].size() != 0 && SIM_INSTR[address + (i * 4)].compare("Invalid Instruction") && preissue[i].size() == 0 && isBranch(address + (i * 4)) == 0 && SIM_INSTR[address + (i * 4)].compare("BREAK"))
                    {
                        preissue[i] = "[" + SIM_INSTR[address + (i * 4)] + "]";
                        bufferDest[0 + i] = instructionDest[address + (i * 4)];
                        bufferSrc1[0 + i] = instructionSrc1[address + (i * 4)];
                        bufferSrc2[0 + i] = instructionSrc2[address + (i * 4)];
                        execute[0 + i] = address + (i * 4);
                    }
                }
            }
            else if (preissue[1].size() == 0)
            {
                if (SIM_INSTR[address].size() != 0 && SIM_INSTR[address].compare("Invalid Instruction") && isBranch(address) == 0 && SIM_INSTR[address].compare("BREAK"))
                {
                    preissue[1] = "[" + SIM_INSTR[address] + "]";
                    bufferDest[1] = instructionDest[address];
                    bufferSrc1[1] = instructionSrc1[address];
                    bufferSrc2[1] = instructionSrc2[address];
                    execute[1] = address;
                }
            }
            LRU[index] = 1;
        }
        else if (LRU[index] == 1)
        {
            outBin[index][1][0] = bit[missList[0]];
            outBin[index][1][1] = bit[missList[1]];
            out[index][1][0] = 1;
            out[index][1][2] = tag;

            if (preissue[0].size() == 0)
            {
                for (int i = 0; i < 2; i++)
                {
                    if (SIM_INSTR[address + (i * 4)].size() != 0 && SIM_INSTR[address + (i * 4)].compare("Invalid Instruction") && preissue[i].size() == 0 && isBranch(address + (i * 4)) == 0 && SIM_INSTR[address + (i * 4)].compare("BREAK"))
                    {
                        preissue[i] = "[" + SIM_INSTR[address + (i * 4)] + "]";
                        bufferDest[0 + i] = instructionDest[address + (i * 4)];
                        bufferSrc1[0 + i] = instructionSrc1[address + (i * 4)];
                        bufferSrc2[0 + i] = instructionSrc2[address + (i * 4)];
                        execute[0 + i] = address + (i * 4);
                    }
                }
            }
            else if (preissue[1].size() == 0)
            {
                if (SIM_INSTR[address].size() != 0 && SIM_INSTR[address].compare("Invalid Instruction") && isBranch(address) == 0 && SIM_INSTR[address].compare("BREAK"))
                {
                    preissue[1] = "[" + SIM_INSTR[address] + "]";
                    bufferDest[1] = instructionDest[address];
                    bufferSrc1[1] = instructionSrc1[address];
                    bufferSrc2[1] = instructionSrc2[address];
                    execute[1] = address;
                }
            }
            LRU[index] = 0;
        }
    }
    missList[0] = 0;
    missList[1] = 0;
}

void fetch(ofstream &ofs, int &address)
{
    istringstream iss;
    string instruction;
    int target;
    bool add = true;

    iss.str(DECODE[address]);
    iss >> instruction;

    for (int i = 0; i < 2; i++)
    {
        if (!instruction.compare("J") == 0)
        {
            if (SIM_INSTR[address].compare("Invalid Instruction") != 0)
            {
                if (accessCache(ofs, address))
                {
                }
                else
                {
                    add = false;
                    address -= 4;
                }
            }
        }
        else if (instruction.compare("J") == 0)
        {
            iss >> target;
            j(target, address);
        }
    }
    if (add)
    {
        address += 4;
    }
}

void issue(int address)
{
    istringstream iss;
    string instruction;
    iss.str(DECODE[execute[0]]);
    iss >> instruction;

    for (int i = 0; i < 4; i++)
    {
        if (hazardChecking(0) == true && preissue[0].size() != 0 && (instruction.compare("LW") == 0 || instruction.compare("SW") == 0))
        {

            if (premem[0].size() == 0)
            {
                premem[0] = preissue[0];
                bufferDest[7] = bufferDest[0];
                bufferSrc1[7] = bufferSrc1[0];
                bufferSrc2[7] = bufferSrc2[0];
                execute[7] = execute[0];
                preissue[0] = preissue[1];
                bufferDest[0] = bufferDest[1];
                bufferSrc1[0] = bufferSrc1[1];
                bufferSrc2[0] = bufferSrc2[1];
                execute[0] = execute[1];
                preissue[1] = "";
                bufferDest[1] = -1;
                bufferSrc1[1] = -1;
                bufferSrc2[1] = -1;
                execute[1] = 0;
            }
            else if (premem[1].size() == 0)
            {
                premem[1] = preissue[0];
                bufferDest[8] = bufferDest[0];
                bufferSrc1[8] = bufferSrc1[0];
                bufferSrc2[8] = bufferSrc2[0];
                execute[8] = execute[0];
                preissue[0] = preissue[1];
                bufferDest[0] = bufferDest[1];
                bufferSrc1[0] = bufferSrc1[1];
                bufferSrc2[0] = bufferSrc2[1];
                execute[0] = execute[1];
                preissue[1] = "";
                bufferDest[1] = -1;
                bufferSrc1[1] = -1;
                bufferSrc2[1] = -1;
                execute[1] = 0;
            }
        }
        else if (hazardChecking(0) == true && preissue[0].size() != 0)
        {
            prealu[0] = preissue[0];
            bufferDest[4] = bufferDest[0];
            bufferSrc1[4] = bufferSrc1[0];
            bufferSrc2[4] = bufferSrc2[0];
            execute[4] = execute[0];
            preissue[0] = preissue[1];
            bufferDest[0] = bufferDest[1];
            bufferSrc1[0] = bufferSrc1[1];
            bufferSrc2[0] = bufferSrc2[1];
            execute[0] = execute[1];
            preissue[1] = "";
            bufferDest[1] = -1;
            bufferSrc1[1] = -1;
            bufferSrc2[1] = -1;
            execute[1] = 0;
        }
    }
    iss.clear();
}

void alu()
{
    if (prealu[0].size() != 0)
    {
        postalu[0] = prealu[0];
        bufferDest[6] = bufferDest[4];
        bufferSrc1[6] = bufferSrc1[4];
        bufferSrc2[6] = bufferSrc2[4];
        execute[6] = execute[4];
        prealu[0] = "";
        bufferDest[4] = -1;
        bufferSrc1[4] = -1;
        bufferSrc2[4] = -1;
        execute[4] = 0;
        memCount = 0;
    }
}

void mem(ofstream &ofs)
{

    istringstream iss;
    string instruction;
    int rt, rs, sa, rd, immediate;

    if (premem[0].size() != 0)
    {
        if (memCount == 1)
        {
            iss.str(DECODE[execute[7]]);
            iss >> instruction;
            if (instruction.compare("LW") == 0)
            {
                iss >> rt >> immediate >> rs;
                missList[0] = immediate;
                missList[1] = immediate + 4;
                missListUpdate(ofs, immediate);
            }
            postmem[0] = premem[0];
            bufferDest[9] = bufferDest[7];
            bufferSrc1[9] = bufferSrc1[7];
            bufferSrc2[9] = bufferSrc2[7];
            execute[9] = execute[7];
            premem[0] = premem[1];
            bufferDest[7] = bufferDest[8];
            bufferSrc1[7] = bufferSrc1[8];
            bufferSrc2[7] = bufferSrc2[8];
            execute[7] = execute[8];
            bufferDest[8] = -1;
            bufferSrc1[8] = -1;
            bufferSrc2[8] = -1;
            premem[1] = "";
            memCount = 0;
        }
        memCount = 1;
    }
}

void wb(ofstream &ofs)
{
    istringstream iss;
    string instruction;
    int rt, rs, sa, rd, immediate;

    iss.str(DECODE[execute[9]]);
    iss >> instruction;
    if (instruction.compare("SW") == 0)
    {
        iss >> rt >> immediate >> rs;
        sw(rt, immediate, rs);
    }

    for (int i = 0; i < 2; i++)
    {

        if (premem[0].size() != 0)
        {
            iss.str(DECODE[execute[7]]);
            iss >> instruction;
            if (instruction.compare("SW") == 0)
            {
                iss >> rt >> immediate >> rs;
                bit[immediate] = REGISTERS[rt];
                missList[0] = immediate;
                missList[1] = immediate + 4;
                missListUpdate(ofs, immediate);
                execute[9] = execute[7];
                execute[7] = -1;
                premem[0] = "";
                bufferDest[7] = -1;
                bufferSrc1[7] = -1;
                bufferSrc2[7] = -1;
            }
            iss.clear();
        }

        if (postmem[0].size() != 0)
        {
            iss.str(DECODE[execute[9]]);
            iss >> instruction;
            if (instruction.compare("SW") == 0)
            {
                iss >> rt >> immediate >> rs;
                sw(rt, immediate, rs);
            }
            else if (instruction.compare("LW") == 0)
            {
                iss >> rt >> immediate >> rs;
                lw(rt, immediate, rs);
            }
            postmem[0] = "";
            bufferDest[9] = -1;
            bufferSrc1[9] = -1;
            bufferSrc2[9] = -1;
        }
        else if (postalu[0].size() != 0)
        {
            iss.str(DECODE[execute[6]]);
            iss >> instruction;
            if (instruction.compare("ADDI") == 0)
            {
                iss >> rt >> rs >> immediate;
                addi(rt, rs, immediate);
            }
            else if (instruction.compare("SW") == 0)
            {
                iss >> rt >> immediate >> rs;
                sw(rt, immediate, rs);
            }
            else if (instruction.compare("LW") == 0)
            {
                iss >> rt >> immediate >> rs;
                lw(rt, immediate, rs);
            }
            else if (instruction.compare("SLL") == 0)
            {
                iss >> rd >> rt >> sa;
                sll(rd, rt, sa);
            }
            else if (instruction.compare("SRL") == 0)
            {
                iss >> rd >> rt >> sa;
                srl(rd, rt, sa);
            }
            else if (instruction.compare("SUB") == 0)
            {
                iss >> rd >> rs >> rt;
                sub(rd, rs, rt);
            }
            else if (instruction.compare("ADD") == 0)
            {
                iss >> rd >> rs >> rt;
                add(rd, rs, rt);
            }
            else if (instruction.compare("MUL") == 0)
            {
                iss >> rd >> rs >> rt;
                mul(rd, rs, rt);
            }
            else if (instruction.compare("SH") == 0)
            {
                iss >> rt >> immediate >> rs;
                sh(rt, immediate, rs);
            }
            else if (instruction.compare("MOVZ") == 0)
            {
                iss >> rd >> rs >> rt;
                movz(rd, rs, rt);
            }
            else if (instruction.compare("OR") == 0)
            {
                iss >> rd >> rs >> rt;
                OR(rd, rs, rt);
            }
            else if (instruction.compare("AND") == 0)
            {
                iss >> rd >> rs >> rt;
                AND(rd, rs, rt);
            }
            postalu[0] = "";
            bufferDest[6] = -1;
            bufferSrc1[6] = -1;
            bufferSrc2[6] = -1;
        }
    }
}

bool hazardChecking(int compare)
{
    bool check = true;

    for (int i = 2; i <= 9; i++)
    {
        if (bufferDest[compare] != -1)
        {
            if (bufferSrc1[compare] == bufferDest[i] || bufferSrc2[compare] == bufferDest[i] || bufferDest[compare] == bufferDest[i])
            {
                check = false;
            }
        }
    }
    return check;
}

void executeBranch(int &address)
{
    istringstream iss;
    string instruction;
    int immediate, rs, rt, rd, sa;
    for (int i = 0; i < 10; i++)
    {
        if (branches[i].size() != 0)
        {
            iss.str(branches[i]);
            iss >> instruction;
            if (instruction.compare("J") == 0)
            {
                iss >> immediate;
                j(immediate, address);
            }
            else if (instruction.compare("BLTZ") == 0)
            {
                iss >> rs >> immediate;
                bltz(rs, immediate, address);
            }
            else if (instruction.compare("BEQ") == 0)
            {
                iss >> rs >> rt >> immediate;
                beq(rs, rt, immediate, address);
            }
            else if (instruction.compare("JR") == 0)
            {
            }
            branches[i] = branches[i + 1];
            branches[i] = "";
        }
    }
}

bool isBranch(int address)
{
    istringstream iss;
    string instruction;
    iss.str(DECODE[address]);
    iss >> instruction;
    if (instruction.compare("J") == 0 || instruction.compare("BLTZ") == 0 || instruction.compare("BEQ") == 0 || instruction.compare("JR") == 0)
    {
        iss.clear();
        for (int i = 0; i < 10; i++)
        {
            if (branches[i].size() == 0)
            {
                branches[i] = DECODE[address];
                return true;
            }
        }
    }
    return false;
}

void add(int rd, int rs, int rt)
{
    REGISTERS[rd] = REGISTERS[rs] + REGISTERS[rt];
}

void sub(int rd, int rs, int rt)
{
    REGISTERS[rd] = REGISTERS[rs] - REGISTERS[rt];
}

void mul(int rd, int rs, int rt)
{
    REGISTERS[rd] = REGISTERS[rs] * REGISTERS[rt];
}

void addi(int rt, int rs, int immediate)
{
    REGISTERS[rt] = REGISTERS[rs] + immediate;
}

void sw(int rt, int offset, int base)
{
    SIM_DATA[REGISTERS[base] + offset] = REGISTERS[rt];
}

void sh(int rt, int offset, int base)
{
    SIM_DATA[REGISTERS[base] + offset] = REGISTERS[rt];
}

void lw(int rt, int offset, int base)
{
    REGISTERS[rt] = SIM_DATA[REGISTERS[base] + offset];
    bit[offset] = SIM_DATA[REGISTERS[base] + offset];
}

void movz(int rd, int rs, int rt)
{
    if (REGISTERS[rt] == 0)
    {
        REGISTERS[rd] = REGISTERS[rs];
    }
}

void OR(int rd, int rs, int rt)
{
    REGISTERS[rd] = (REGISTERS[rs] | REGISTERS[rt]);
}

void AND(int rd, int rs, int rt)
{
    REGISTERS[rd] = (REGISTERS[rs] & REGISTERS[rt]);
}

void beq(int rs,
         int rt, int offset, int &i)
{
    if (REGISTERS[rs] == REGISTERS[rt])
    {
        i = offset;
    }
}

void bltz(int rs, int offset, int &i)
{
    if (REGISTERS[rs] < 0)
    {
        i += (offset + 4);
    }
}

void sll(int rd, int rt, int sa)
{
    REGISTERS[rd] = REGISTERS[rt] * (sa * 2);
}

void srl(int rd, int rt, int sa)
{
    REGISTERS[rd] = REGISTERS[rt] / (sa * 2);
}

void jr(int rs, int &i)
{
    i = rs;
}

void j(int target, int &i)
{
    i = (target - 4);
}