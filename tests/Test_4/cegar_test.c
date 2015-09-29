int r = 0;

void f(int x){	
  r++;
}

int main(){
int x = 0;

while (1){
	x ++;
	if (x == 2 || x == 9) f(x);

}

return 0;

}
