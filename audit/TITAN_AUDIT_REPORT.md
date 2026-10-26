# titan-audit report: `fefferman-clay-navier-stokes`

**Verdict: PASS_WITH_WARNINGS**

- Generated (UTC): 2026-10-26T00:00:47+00:00
- Tool: titan-audit 1.0.0 (Benjamin Stanley Frohman (ORCID: 0009-0006-7068-3718))
- Toolchain: `leanprover/lean4:v4.30.0-rc1`  Git HEAD: `None`
- Tree SHA-256: `76738ff08b99b5e1cf1799fd4a6aaba6307de79d1a8cd158209fa4b305c02538` over 9 files

## Build

- Build skipped (`--no-build`); audit used existing .olean files.

## Axiom audit

- Modules: 5  Theorems: 184  Clean (only propext/Classical.choice/Quot.sound): 184
- Nonstandard: 0

| Module | Theorems | Nonstandard |
|---|---:|---:|
| `FeffermanClayNS.Defs` | 143 | 0 |
| `FeffermanClayNS.FeffermanStatements` | 13 | 0 |
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

- ed25519 public key (base64): `c7BnJCTBz91GSJfR9q9g7XaE9b8u6r2wfKeXGzYuwKs=`
- Verify: `titan-audit verify report.json`
