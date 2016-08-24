int f(int s) { 
	return s ++;
	
}

int g(int s) {
	s = 1;
	s = 0;
	return s;
}

int main() {
  int i = 10, x=0;

  while(i != 0){
    i--;
    if(x) x = f(x);
    x = g(x);
  } 
 return 0;

}
