# titan-audit report: `fefferman-clay-navier-stokes`

**Verdict: PASS_WITH_WARNINGS**

- Generated (UTC): 2026-10-30T19:03:51+00:00
- Tool: titan-audit 1.0.0 (Benjamin Stanley Frohman (ORCID: 0009-0006-7068-3718))
- Toolchain: `leanprover/lean4:v4.30.0-rc1`  Git HEAD: `8ac440d5bcea80d9f7e52529ed758988ec2a92dd`
- Tree SHA-256: `eaa1cb3091fd459716555874665031ef7563a7aeb2727ed3dc5685c0663c6cd5` over 12 files

## Build

- Build skipped (`--no-build`); audit used existing .olean files.

## Axiom audit

- Modules: 8  Theorems: 258  Clean (only propext/Classical.choice/Quot.sound): 258
- Nonstandard: 0

| Module | Theorems | Nonstandard |
|---|---:|---:|
| `FeffermanClayNS.Defs` | 148 | 0 |
| `FeffermanClayNS.FeffermanStatements` | 13 | 0 |
| `FeffermanClayNS.FinalProductTheorem` | 24 | 0 |
| `FeffermanClayNS.HighSetDepletionAndBKM` | 15 | 0 |
| `FeffermanClayNS.MainTheorem` | 4 | 0 |
| `FeffermanClayNS.Stage6Calculus` | 35 | 0 |
| `FeffermanClayNS.TorusStrainExclusion` | 19 | 0 |

## Source scan

Counts: real_iSup_without_BddAbove=4


### Vacuity heuristics (in build)

- real_iSup_without_BddAbove `FeffermanClayNS/Defs.lean:2291` `Tstar`: Real iSup/sSup is 0 on unbounded ranges; downstream bounds on it may be vacuous unless BddAbove is required.
- real_iSup_without_BddAbove `FeffermanClayNS/Defs.lean:2802` `vorticity_sup_norm`: Real iSup/sSup is 0 on unbounded ranges; downstream bounds on it may be vacuous unless BddAbove is required.
- real_iSup_without_BddAbove `FeffermanClayNS/Defs.lean:2816` `strain_sup_norm`: Real iSup/sSup is 0 on unbounded ranges; downstream bounds on it may be vacuous unless BddAbove is required.
- real_iSup_without_BddAbove `FeffermanClayNS/HighSetDepletionAndBKM.lean:366` `periodicTstar`: Real iSup/sSup is 0 on unbounded ranges; downstream bounds on it may be vacuous unless BddAbove is required.

Heuristics are advisory: a flag means *look here*, not *wrong*.

## Signature

- ed25519 public key (base64): `YoEHEghXFxrXvYKQoWQb+oDunzwdxBgpk03gxrdC7WI=`
- Verify: `titan-audit verify report.json`
