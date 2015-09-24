#include <stdlib.h>
#include <time.h>

int x = 0;
int y = 10;

void f(){
  while (x<50){
    x++;
    y--;
  }


while (x>1){
    x-= 2;
    y += 2;
}
  return;
}

int main(){

  f();
return 0;
}
