# titan-audit report: `fefferman-clay-navier-stokes`

**Verdict: PASS_WITH_WARNINGS**

- Generated (UTC): 2026-10-28T23:16:13+00:00
- Tool: titan-audit 1.0.0 (Benjamin Stanley Frohman (ORCID: 0009-0006-7068-3718))
- Toolchain: `leanprover/lean4:v4.30.0-rc1`  Git HEAD: `3abe9bcb0be7ebe9a397af765efaea097af83238`
- Tree SHA-256: `6cc2ef08d941398c5bd910c33453148ad8a7e5be64d91903658b7c7b0b35b123` over 12 files

## Build

- Build skipped (`--no-build`); audit used existing .olean files.

## Axiom audit

- Modules: 7  Theorems: 0  Clean (only propext/Classical.choice/Quot.sound): 0
- Nonstandard: 0

| Module | Theorems | Nonstandard |
|---|---:|---:|

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
