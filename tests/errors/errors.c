
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

void call_hello_uninit(int hx) {
  int bc; 
  private_hello(0, bc);
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

int two_errors(int x, int a) {
  if(a) {
    return x + 1;
  }
  return x + 2;
}

int one_unreachable(int x, int y) {
  if(x ==0) {
    if(x == 1) {
      return y + 1;
    }
  }
  return x + 2;
}

int after_conds(int x, int y) {
  if(y==3) {
    y = 0;
  }else {
    y = 1;
  }
  return x + 1;
}


int two_backedges(int x) {
  while(1) {
    if(x == 4) {
    }else {
      if(x >= 0){
        break;
      }
    }
  }
  return x + 12;
}

int error_both_paths(int x, int y) {
  if(x) {
    return y + 10;
  }else {
    return y + 3;
  }
  return 0;
}

int error_both_paths1(int x, int y) {
  int r = 0; 
  if(x) {
    r = y + 10;
  }else {
    r = y + 15;
  }
  return y;
}
