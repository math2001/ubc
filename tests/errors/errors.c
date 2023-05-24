int uninit() {
  int x;
  return x;
}

int overflow(int x) {
  return x + 1;
}

int underflow(int x) {
  return x - 1;
}


int overflow1(int x) {
  return x + (23 + 234);
}


int overflow2(int x, int y) {
  return y+23+(x+45);
}

int overflow3(int x, int y, int z) {
  return x + y + z;
}

int overflow_underflow(int x, int y) {
  return x + (y - 45);
}


// Helper -> Assume free from UBC 
int private_hello(int hx, char hc) { 
  hx = hx >> hx;
  hx = hx + 5;
  return hx;
}


void call_hello(int hx, char bc) {
  if(bc) {
    private_hello(hx, bc);
    return;
  }
  return;
}

int add1(int x) {
  return x;
}


int deep_failure(int dfx, char p1, char p2, char p3, char p4) {
  if(dfx > 3) {
    if(p2) {
      if(p3) {
        return 96; 
      }else {
        return dfx + 96;
      }
    } 
    return 1;
  }else {
    if(p1) {
      return 2;
    }
    return 3;
  }
}


void call_hello_failure(char cchf) {
  int x;
  if(cchf) {
    private_hello(x, cchf);
  }
  return;
}

int after_loop(int x, int y) {
  while(1) {
    if(x == 10) {
      break;
    }
  }
  return y + 10;
}


int after_loop_conditionals(int x, int y, int z) {
  while(1) {
    if(x == 20) {
      while(1) {
        if(y == 10) {
          break;
        }
      }
      break;
    }
    return z;
  }
  return z + 34;
}


int times(int x,int y) {
  return x * y;
}


int combined_overflow_ops(int x, int y) {
  int r = x << 4;
  return r + y;
}
