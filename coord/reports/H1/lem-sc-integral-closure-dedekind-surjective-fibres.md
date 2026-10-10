Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-integral-closure-dedekind-surjective-fibres.json`: split item, no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-sc-krull-akizuki-noetherian.json`: statement-only unsplit node, no Mathlib match.
- `citations.json`: verbatim citations for every proof-step dependency.

Attachments:

- `lem-weil-pbc-integral-injective-dimension-equal` is an existing reviewed node for Stacks 00OK (dimension preservation).
- `lem-weil-pbc-integral-closure-finite-extension-normal` is an existing Mathlib leaf for normality, domain, and fraction field of the integral closure.
- `lem-weil-pbc-integral-injective-lying-over` is an existing Mathlib leaf for Stacks 00GQ (surjectivity).
- `lem-weil-pbc-dim-one-residue-field-extensions-finite` is an existing reviewed node for Stacks 031F (finite primes over a maximal ideal and finite residue extensions).
- `lem-weil-pbc-integral-incomparability` is an existing node used to identify the unique generic prime.

WANTED: none.

## Review by H1

I read the target source at the Stacks Project page for Algebra Lemma 10.120.18, Tag 09IG, and verified its linked inputs: Krull–Akizuki Tag 00PG, dimension preservation Tag 00OK, the Dedekind characterization Tag 034X, lying-over Tag 00GQ, and the local finite-fibre/residue-field lemma Tag 031F. The item statement matches 09IG clause by clause: Noetherian one-dimensional domain A, finite fraction-field extension L/K, integral closure C, Dedekind conclusion, surjective spectrum map, finite fibres, and finite residue extensions.

Step 1 uses the new 00PG node exactly: C is an intermediate ring A ⊆ C ⊆ L, so it is Noetherian. Step 2 uses the existing dimension-equality node for the injective integral inclusion A ⊆ C and the existing normal-integral-closure leaf for the domain, integrally closed, and fraction-field clauses; the hypotheses are the target hypotheses and C ⊆ L. Step 3 uses the existing lying-over node, with the same injective integral inclusion, to obtain surjectivity. Step 4 localizes A and C at A\\m for each maximal m; the resulting map satisfies every hypothesis of the existing 031F node, and localization identifies its primes and residue fields with those of C over m. The generic fibre is handled separately: incomparability forces a prime of C contracting to (0) to equal (0), since C is a domain. The cited lying-over statement supplies existence, while 031F supplies finiteness and residue extensions over closed points.

I searched the whole DAG and blueprint before creating the only new node. No existing node states Krull–Akizuki for arbitrary intermediate rings; the 031F statement already exists and is cited rather than duplicated. I ran LeanFinder, Loogle, and Mathlib grep searches for both the item and the new 00PG node; Mathlib has only stronger or differently hypothesized integral-closure results, so neither is a Mathlib leaf. Small-case checks include C=A (identity extension), L=K, and A a DVR: the proof reduces to the identity map, one generic prime, and the finite closed fibres supplied by 031F.

The correction made during review was to avoid applying 031F directly to the nonlocal ring C: both rings are localized at A\\m first. I also added the incomparability citation for the generic-fibre uniqueness argument and corrected the blueprint via entry to the existing `lem-sc-dim-one-ample-invertible` id.

Not duplicates:

- `lem-sc-krull-akizuki-noetherian` vs `lem-weil-pbc-integral-closure-finite-extension-normal`: the former covers arbitrary intermediate rings and only Noetherianity; the latter covers normality and fraction fields of an integral closure under finite extension.
- `lem-sc-integral-closure-dedekind-surjective-fibres` vs `lem-sc-semilocal-dim-one-normalization`: the item allows a finite extension L/K and asserts surjectivity, finite fibres, and residue extensions; the existing normalization node specializes to L=K and additionally derives semilocality and equality of fraction fields.

## Second reading by H1

- Item statement: checked against Stacks Algebra Lemma 09IG (tag 09IG), hypothesis by hypothesis; matches.
- New node `lem-sc-krull-akizuki-noetherian`: checked against Algebra Lemma 10.119.12 (tag 00PG); self-contained statement, definitions, TeX, and recorded searches pass.
- Step 1: checked the 00PG statement supplies Noetherianity for the intermediate ring C; verdict correct.
- Step 2: checked the 00OK and integral-closure normality statements supply dimension, domain, integrally closed, and fraction-field claims; verdict correct.
- Step 3: checked the 00GQ lying-over statement supplies surjectivity; verdict correct.
- Step 4: checked the 031F hypotheses after localization, the existing localization prime correspondence and residue-field isomorphism nodes, and 00GT incomparability; generic residue extension is explicitly L/K; verdict correct.
- Small cases checked: C=A and L=K give the identity map; A a DVR gives one generic point and finite closed fibres; the generic fibre residue extension is K/K in the identity case.
- Changes: expanded step 4 with the explicit localization prime and residue-field argument (avoiding an undeclared cross-unit tool), made the generic residue extension explicit, and retained only the unit's established dependencies.
