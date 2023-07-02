# Homotopy Type Theory (OPLSS 2023)

## Resources

### Textbooks
1. [The HoTT Book](https://homotopytypetheory.org/book/)
2. [Introduction to HoTT](https://arxiv.org/abs/2212.11082), Egbert Rijke

### Expository papers
1. [An introduction to univalent foundations for mathematicians
](https://arxiv.org/abs/1711.01477v3), Daniel R. Grayson
2. [Homotopy type theory: the logic of space](https://arxiv.org/abs/1703.03007), Michael Shulman

### Original papers
1. [Intuitionistic type theory](https://archive-pml.github.io/martin-lof/pdfs/Bibliopolis-Book-retypeset-1984.pdf), Per Martin-Löf (Lecture 1)


## UniMath (Coq)

Exercises can be done on paper or using the UniMath library in the Coq proof assistant. (Or other libraries in other proof assistants if you dare!) Here are instructions for installing/using the UniMath library in the Coq proof assistant in order from easiest to hardest.

1. Use an in-browser implementation: https://unimath.github.io/live/
  - This was just released especially for this course! I've tested it with the exercises, and it works great for me with Chrome on MacOS (but not Safari). If there are any problems, it would be appreciated if you could report them here: https://github.com/UniMath/UniMath/discussions/1729.

2. Use the UniMath binaries provided with recent distributions of Coq + VSCode: https://docs.google.com/document/d/1KWSugPK-sJ67pL-P4EtoKZ6HMzewmzewLNkR_arXauY/edit?usp=sharing
  - Note that where there are paths like `/Applications/Coq-Platform~8.15~2022.04.app/Contents/Resources/bin` you need to check that this is where Coq is installed on your computer. In particular, if you have installed it recently, it will be something more like `Coq-Platform~8.16~2022.09.app`.
  - Also make sure to remove or comment out the custom VS Code settings whenever you want to work with vanilla Coq.

3. Compile UniMath yourself + use Emacs: https://github.com/UniMath/UniMath/blob/master/INSTALL.md
- You will want to have the source code of the UniMath library on your computer if you ever want to contribute to it.
- Also note that it is possible to mix up the instructions in 2 and 3, i.e. to compile UniMath yourself and use VSCode, or use the provided UniMath binaries with Emacs.

