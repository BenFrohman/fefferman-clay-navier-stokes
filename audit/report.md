# titan-audit report: `fefferman-clay-navier-stokes`

**Verdict: PASS_WITH_WARNINGS**

- Generated (UTC): 2026-10-30T19:19:09+00:00
- Tool: titan-audit 1.0.0 (Benjamin Stanley Frohman (ORCID: 0009-0006-7068-3718))
- Toolchain: `leanprover/lean4:v4.30.0-rc1`  Git HEAD: `1869c1ac0d1fd61b076f66ffa059757a342c2968`
- Tree SHA-256: `65634766800aec9789f41682ed7b301bf3d0658daa7aabc17029d5b61799358a` over 12 files

## Build

- Build skipped (`--no-build`); audit used existing .olean files.

## Axiom audit

- Modules: 8  Theorems: 269  Clean (only propext/Classical.choice/Quot.sound): 269
- Nonstandard: 0

| Module | Theorems | Nonstandard |
|---|---:|---:|
| `FeffermanClayNS.Defs` | 148 | 0 |
| `FeffermanClayNS.FeffermanStatements` | 13 | 0 |
| `FeffermanClayNS.FinalProductTheorem` | 24 | 0 |
| `FeffermanClayNS.HighSetDepletionAndBKM` | 26 | 0 |
| `FeffermanClayNS.MainTheorem` | 4 | 0 |
| `FeffermanClayNS.Stage6Calculus` | 35 | 0 |
| `FeffermanClayNS.TorusStrainExclusion` | 19 | 0 |

## Source scan

Counts: real_iSup_without_BddAbove=5


### Vacuity heuristics (in build)

- real_iSup_without_BddAbove `FeffermanClayNS/Defs.lean:2291` `Tstar`: Real iSup/sSup is 0 on unbounded ranges; downstream bounds on it may be vacuous unless BddAbove is required.
- real_iSup_without_BddAbove `FeffermanClayNS/Defs.lean:2802` `vorticity_sup_norm`: Real iSup/sSup is 0 on unbounded ranges; downstream bounds on it may be vacuous unless BddAbove is required.
- real_iSup_without_BddAbove `FeffermanClayNS/Defs.lean:2816` `strain_sup_norm`: Real iSup/sSup is 0 on unbounded ranges; downstream bounds on it may be vacuous unless BddAbove is required.
- real_iSup_without_BddAbove `FeffermanClayNS/HighSetDepletionAndBKM.lean:374` `periodicTstar`: Real iSup/sSup is 0 on unbounded ranges; downstream bounds on it may be vacuous unless BddAbove is required.
- real_iSup_without_BddAbove `FeffermanClayNS/HighSetDepletionAndBKM.lean:501` `periodicTstarOriginal`: Real iSup/sSup is 0 on unbounded ranges; downstream bounds on it may be vacuous unless BddAbove is required.

Heuristics are advisory: a flag means *look here*, not *wrong*.

## Signature

- ed25519 public key (base64): `YoEHEghXFxrXvYKQoWQb+oDunzwdxBgpk03gxrdC7WI=`
- Verify: `titan-audit verify report.json`
