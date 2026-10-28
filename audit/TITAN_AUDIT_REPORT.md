# titan-audit report: `fefferman-clay-navier-stokes`

**Verdict: PASS_WITH_WARNINGS**

- Generated (UTC): 2026-10-28T22:04:10+00:00
- Tool: titan-audit 1.0.0 (Benjamin Stanley Frohman (ORCID: 0009-0006-7068-3718))
- Toolchain: `leanprover/lean4:v4.30.0-rc1`  Git HEAD: `6954ea6de11b01d465e392643204300581259f3f`
- Tree SHA-256: `8b0ce83c0df2724bdff9f7c137ec9f71a00ac488d27074b99945ffda2a795d9f` over 10 files

## Build

- Build skipped (`--no-build`); audit used existing .olean files.

## Axiom audit

- Modules: 6  Theorems: 208  Clean (only propext/Classical.choice/Quot.sound): 208
- Nonstandard: 0

| Module | Theorems | Nonstandard |
|---|---:|---:|
| `FeffermanClayNS.Defs` | 143 | 0 |
| `FeffermanClayNS.FeffermanStatements` | 13 | 0 |
| `FeffermanClayNS.FinalProductTheorem` | 24 | 0 |
| `FeffermanClayNS.HighSetDepletionAndBKM` | 9 | 0 |
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
