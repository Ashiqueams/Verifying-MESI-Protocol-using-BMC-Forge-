# Bounded Model Checking of a Simplified MESI Cache Coherence Protocol in Forge

**CS 6110 | Ashique Mohammad & Muntaha Tasnim**

---

## Requirements

- Racket: https://racket-lang.org
- Forge: `raco pkg install forge`
- VSCode + Forge extension (`SiddharthaPrasad.forge-fm`) recommended

---

## How to Run

Open `mesi_final_v4.frg` in VSCode and click the **Run** button (top right).
Sterling will open automatically in your browser.

Or from terminal:
```bash
racket mesi_final_v4.frg
```

---

## Reproducing the Demo

Use the **dropdown in the top-right** of Sterling
to navigate between commands and click on Run. Here is what to expect:

| Instance | Command | Expected |
|---|---|---|
| 1 | Run — sanity check | Satisfiable — valid initial state |
| 2 | Check — atMostOneModified | **Unsatisfiable** |
| 3 | Check — full SWMR ← main result | **Unsatisfiable** |
| 4 | Check — noModifiedAndShared | **Unsatisfiable** |
| 5 | Check — ordering safety | **Unsatisfiable** |
| 6 | Run — BusUpgr witness | Satisfiable |
| 7 | Run — all Shared witness | Satisfiable |
| 8 | Run — write witness | Satisfiable |