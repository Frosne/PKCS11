#include <stdio.h>
#include <stdbool.h>

void * null_ptr = (void*) 0;

struct exceptionTable
{
	int number;
	char exception[20];
};

struct CK_C_INITIALIZE_ARGS 
{
	void* createMutex;
	void* deleteMuutex;
	void* lockMutex;
	void* unlockMutex;
	bool flags[2];
	void* pReserved;
};


struct CK_C_INITIALIZE_ARGS1
{
	void* (*createMutex)(void*);
	void* (*deleteMutex)(void*);
	void* (*lockMutex)(void*);
	void* (*unlockMutex)(void*);
	bool flags[2];
	void* pReserved;
};

int CK_C_INITIALIZE(struct CK_C_INITIALIZE_ARGS * a)
{
	//...
	return 0;
}

int main()
{
	bool fl = {true, true};
	struct CK_C_INITIALIZE_ARGS something = {null_ptr, null_ptr, null_ptr, null_ptr, fl, null_ptr };
	struct CK_C_INITIALIZE_ARGS * CK_C_INITIALIZE_ARGS_PTR1 = &something;
	struct CK_C_INITIALIZE_ARGS * CK_C_INITIALIZE_ARGS_PTR = 0;

	return CK_C_INITIALIZE (CK_C_INITIALIZE_ARGS_PTR);

}