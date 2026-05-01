# POPGEN

Methods for deordering and reordering partial order causal link (POCL) plans.

## Usage

```bash
# Assuming you have uv already installed
$ uv venv
$ uv sync

# Encode a given problem+plan into a MaxSAT instance
$ python popgen/encoder.py --domain d.pddl --problem p.pddl --plan p.plan --output out.wcnf

# Solve the MaxSAT instance
$ rc2.py -vv out.wcnf > out.sol

# Decode the solution back into a plan
$ python popgen/analyzer.py --map out.wcnf.map --rc2out out.sol --print-solution --show-popstats --count-linearizations --dot plan.dot
```

## Requirements

- [pysat](https://pysathq.github.io/)
- [bauhaus](https://bauhaus.readthedocs.io/)

## Citing This Work

```latex
@article{jair-popgen,
  author    = {Christian Muise and J. Christopher Beck and Sheila A. McIlraith},
  title     = {Optimal Partial-Order Plan Relaxation via MaxSAT},
  journal   = {Journal of Artificial Intelligence Research},
  year      = {2016},
  url       = {http://www.jair.org/media/5128/live-5128-9534-jair.pdf}
}
```

This repository extends POPGEN with support for general partial-order plans via white knight constraints. If you use this functionality, please additionally cite:
```latex
@InProceedings{Oates2026WhiteKnights,
  author    = {Harrison Oates and Pascal Bercher},
  booktitle = {IJCAI-ECAI 2026},
  title     = {Are White Knights Worth the Trouble? Reconciling POCL and Partial-Order Plans for Plan Optimization},
  year      = {2026},
  publisher = {IJCAI Organization}
}
```
