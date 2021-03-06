# XYSyGus

> 作者：刘德欣 孙培艺
>
> 此项目为 软件分析技术2018年秋 的课程项目。目标为根据syntax进行程序生成。
>
> Github： https://github.com/XYPTATeam/XYSyGus.git

## 1. 基本思路

我们的基本框架沿袭自枚举法的自顶向下枚举。

- 从输出开始枚举，按照语法依次展开。
- 采用广度优先搜索的方式进行语法规则式的展开。
- 在广度优先搜索时，可以采用排序加速最优结果的产生。对非终结符进行排序，同时也对产生式进行排序。
- 通过SMT求解器判断程序是否等价， 以及验证程序的正确性（是否满足Constraint规则）。

## 2. 加速方式

我们从两种角度进行加速。

- 从程序正确性的验证角度。运用基于CEGIS的思路进行验证。
  - 与传统的CEGIS不同，我们将约束求解器返回的正例和反例都作为测试输入保存。
  - 保存反例：可以更快的检测出当前的程序结构是不是符合。
  - 保存正例：虽然正例不一定能够快速有效的检测程序是不是符合要求，但是由于之前获得的正例可能更有利于反映代码结构，所以我们也保存了正例，进行枚举的加速。
- 从广度优先搜索时的排序角度。运用从Constraint中抽取的暗示进行验证。
  - 枚举法需要选择一条语句进行扩展，在决定优先针对什么语句进行探索，以及如何进行探索时，我们采用基于Constraint预测的方法。
  - 我们基于如下假设：Constraint的结构可能和它期望生成的代码结构有关。因此我们会从constraint中抽取可能对代码生成的暗示，利用这些暗示针对性的生成程序。
  - 我们会保存一组Constraint的所有用到的比较运算、用到的常数、用到的变量。
  - 我们同时还保存了每个基本运算符可能出现的位置，比如`max2`常常出现在`<=`的两边。
  - 在进行BFS对一条语句进行扩展时，我们将基于是否符合以上暗示，对语句进行排序。选择最符合的一条语句进行探索。

## 3. 代码结构

```sh
CEGIS/
	hint.py  	  #利用Constraint中的暗示进行加速
	cegis.py 	  #利用CEGIS进行加速
	main.py  	  #程序入口
	translator.py #syn2语言与使用list表示的语法树间转换
```

## 4. 使用方法

```sh
python main.py path_to_sl
```

## 5. 实验结果

基于`open_tests`数据进行验证，通过(33/33)。实验结果如下：

~~~sh
./tests/open_tests/array_search_10.sl:Passed(0.857000)
./tests/open_tests/array_search_11.sl:Passed(0.889000)
./tests/open_tests/array_search_12.sl:Passed(0.860000)
./tests/open_tests/array_search_13.sl:Passed(0.940000)
./tests/open_tests/array_search_14.sl:Passed(0.932000)
./tests/open_tests/array_search_15.sl:Passed(0.994000)
./tests/open_tests/array_search_2.sl:Passed(0.721000)
./tests/open_tests/array_search_3.sl:Passed(0.752000)
./tests/open_tests/array_search_4.sl:Passed(0.716000)
./tests/open_tests/array_search_5.sl:Passed(0.746000)
./tests/open_tests/array_search_6.sl:Passed(0.798000)
./tests/open_tests/array_search_7.sl:Passed(0.761000)
./tests/open_tests/array_search_8.sl:Passed(0.835000)
./tests/open_tests/array_search_9.sl:Passed(0.807000)
./tests/open_tests/max10.sl:Passed(0.825000)
./tests/open_tests/max12.sl:Passed(1.116000)
./tests/open_tests/max13.sl:Passed(1.255000)
./tests/open_tests/max14.sl:Passed(2.016000)
./tests/open_tests/max15.sl:Passed(2.185000)
./tests/open_tests/max2.sl:Passed(0.733000)
./tests/open_tests/max3.sl:Passed(0.797000)
./tests/open_tests/max4.sl:Passed(0.729000)
./tests/open_tests/max5.sl:Passed(0.740000)
./tests/open_tests/max6.sl:Passed(0.773000)
./tests/open_tests/max7.sl:Passed(0.758000)
./tests/open_tests/max8.sl:Passed(0.816000)
./tests/open_tests/max9.sl:Passed(0.792000)
./tests/open_tests/max_11.sl:Passed(0.973000)
./tests/open_tests/s1.sl:Passed(0.727000)
./tests/open_tests/s2.sl:Passed(0.725000)
./tests/open_tests/s3.sl:Passed(0.778000)
./tests/open_tests/three.sl:Passed(9.928000)
./tests/open_tests/tutorial.sl:Passed(0.753000)
~~~

