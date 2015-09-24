#include <stdlib.h>
#include <time.h>

int x = 0;
int y = 0;
int z = 0;

void f(){
	x++;
}

void g(){
	y++;
}

void h() {
	z++;
}

int main(){
srand(time(NULL));

while(rand()%2){
	switch (rand() % 3) {
		case 0: f(); break;
		case 1: g(); break;
		default: h(); break;
		}
	}
return 0;

}
