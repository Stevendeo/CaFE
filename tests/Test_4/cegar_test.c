int r = 0;

void f(int x){	
  r++;
}

int main(){
int x = 0;
// if (rand()%2) x = 8;

while (x<10){
	x ++;
	if (x == 2 || x == 7) f(x);

}

return 0;

}
// AFM2012 Yannick Moy
// G = ts les points
