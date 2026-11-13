# predictive

Code for the experiment in Section 11 of `Lattice/main.tex`: exact tools for stochastic processes
and their predictive monoids, and the training and readout code.

| Module | Contents |
|---|---|
| `linalg.py` | Exact linear algebra over the rationals |
| `ghmm.py` | GHMM / HMM operators, word probabilities, Hankel rank, the canonical predictive machine |
| `processes.py` | Named processes, including the action processes `act_s3`, `act_z6`, `act_s4`, `act_a5`, `act_ap5`, `act_latch`, `act_latch4`, `act_latchwalk`, and `z1r`, `rrxor` |
| `monoid.py` | The transition monoid `S_p`: size, aperiodicity, largest cyclic period |
| `dataset.py` | Every possible context of a fixed length with its exact next-symbol law |
| `train.py` | Small transformers trained in parallel |
| `lengthgen.py` | Next-symbol training at every position, loss by position beyond the trained length |
| `monoidprobe.py` | Readouts of monoid elements and predictive states from the residual stream |
| `a2report.py` | Tables and the length-generalisation figure |

The exact modules need only the standard library. Training needs PyTorch.

```bash
python -m pytest tests
```

Results and the commands that reproduce them are in [`results/a2/README.md`](../results/a2/README.md).
