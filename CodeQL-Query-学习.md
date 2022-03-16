# CodeQL-Query-学习

## 前言

感觉想写出比较好的查询还是需要对CodeQL和AST有非常深刻的了解，所以还是得好好学习学习。记录下语法学习以及各种查询的编写。



## 各种编写

判断函数返回值为void

```java
class FastJsonSetMethod extends Method{
  FastJsonSetMethod(){
    exists(VoidType vt|
      vt = this.getReturnType()
      )
  }
}
```

函数参数数量(this为method)

```java
this.getNumberOfParameters() = 0
```



获取函数所属的类：

```java
getDeclaringType()
```





