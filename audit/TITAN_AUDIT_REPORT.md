# titan-audit report: `fefferman-clay-navier-stokes`

**Verdict: PASS_WITH_WARNINGS**

- Generated (UTC): 2026-10-28T23:10:10+00:00
- Tool: titan-audit 1.0.0 (Benjamin Stanley Frohman (ORCID: 0009-0006-7068-3718))
- Toolchain: `leanprover/lean4:v4.30.0-rc1`  Git HEAD: `ea51748e4af2959cc401a3c931df841f98a9e178`
- Tree SHA-256: `b716fcde0ade8ee2206eaf983e5bb07156c54b9ee3a0eaf67b4a6a5c57010e4c` over 12 files

## Build

- Build skipped (`--no-build`); audit used existing .olean files.

## Axiom audit

- Modules: 8  Theorems: 225  Clean (only propext/Classical.choice/Quot.sound): 225
- Nonstandard: 0

| Module | Theorems | Nonstandard |
|---|---:|---:|
| `FeffermanClayNS.Defs` | 143 | 0 |
| `FeffermanClayNS.FeffermanStatements` | 13 | 0 |
| `FeffermanClayNS.FinalProductTheorem` | 24 | 0 |
| `FeffermanClayNS.HighSetDepletionAndBKM` | 9 | 0 |
| `FeffermanClayNS.MainTheorem` | 1 | 0 |
| `FeffermanClayNS.Stage6Calculus` | 16 | 0 |
| `FeffermanClayNS.TorusStrainExclusion` | 19 | 0 |

## Source scan

Counts: real_iSup_without_BddAbove=3


### Vacuity heuristics (in build)

- real_iSup_without_BddAbove `FeffermanClayNS/Defs.lean:2290` `Tstar`: Real iSup/sSup is 0 on unbounded ranges; downstream bounds on it may be vacuous unless BddAbove is required.
- real_iSup_without_BddAbove `FeffermanClayNS/Defs.lean:2801` `vorticity_sup_norm`: Real iSup/sSup is 0 on unbounded ranges; downstream bounds on it may be vacuous unless BddAbove is required.
- real_iSup_without_BddAbove `FeffermanClayNS/Defs.lean:2815` `strain_sup_norm`: Real iSup/sSup is 0 on unbounded ranges; downstream bounds on it may be vacuous unless BddAbove is required.

Heuristics are advisory: a flag means *look here*, not *wrong*.

## Signature

- ed25519 public key (base64): `ZOyujV1yUEldQRZEDhmXCHa4ikWGfcTD+meZYssNLpo=`
- Verify: `titan-audit verify report.json`
