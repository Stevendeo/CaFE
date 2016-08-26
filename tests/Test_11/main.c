#include<stdlib.h>

void f1 ()
{return ;}

void f2(){return ;}

int main(){
void (*p1)(void) = (f1);
void (*p2)(void) = (f2);
int x = 0;

while (x < 10){
  x++;
  (*p2)();
  if (rand())
    {(*p1)();}
  

}

}
