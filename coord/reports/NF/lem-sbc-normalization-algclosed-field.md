1. Files written: item `lem-sbc-normalization-algclosed-field` (statement, split); new node `lem-sbc-integral-closure-algclosed-fraction` (statement, Mathlib exact leaf `IsFractionRing.isAlgClosed_integralClosure`, Mathlib/FieldTheory/IsAlgClosed/Basic.lean:149).
2. Attachments: `IsFractionRing.isAlgClosed_integralClosure` supplies the new node `lem-sbc-integral-closure-algclosed-fraction`. `AlgebraicGeometry.Etale.exists_normalization_of_isAlgClosed` at `CurveTestDatum.lean:126` is sorry-backed (its proof reaches the later sorry), so it cannot attach.
3. WANTED: none.
4. Repair: removed the prior node's restatement of local normality and made it only the ring-theoretic fraction-field lemma. The parent proof now cites the existing finite-product integral-closure normality node for localizations, and spells out the algebraic-closure argument and the integral morphism construction. This addresses D1/D2 by retaining the substantive affine algebraic argument in the parent. The source's normalization theorem ends at lines 126–167; the sorry at line 198 belongs to the following coefficient theorem, as required by F1.
5. Nothing remains unfinished for this stage.

## Review by NF
I read `sbc-lem-bc-universal-test.md` (final normalization sentence), Stacks Tags 035H, 035I, 035L and 0F08, and `CurveTestDatum.lean:126–167`. The item statement preserves the original affine base, integral closure in the image inside K, normal local rings, algebraically closed function field, lift equation and dominance. Step 1 is the affine-spectrum construction. Step 2 uses the new fraction-field node, the existing finite-product integral-closure normality node (one-factor specialization), and the definitions of integral scheme, normal ring and integral morphism; these citations state the exact domain/localization and integrality facts used. Step 3 identifies the function field with Frac(B), applies the new node's algebraic-closedness and embedding, and explains the root/denominator argument. Step 4 uses contravariance of Spec and injectivity for the generic point and dominance. I checked the new lemma on A=K, on Q→C, and on polynomial subrings; no degenerate case changes the conclusion. Fresh LeanFinder, Loogle, grep and unavailable LeanSearch searches were run for both the item and new node and recorded in their mathlib_searches.

## Not duplicates
lem-sbc-integral-closure-algclosed-fraction vs lem-sbc-integral-closure-finite-normal-product: the new node proves algebraic closedness and the field embedding; the existing node proves normal localizations of finite-product integral closures.
lem-sbc-integral-closure-algclosed-fraction vs lem-sbc-normal-finite-stage-universal: ring-theoretic field statement versus finite-stage universal normalization.
lem-sbc-integral-closure-algclosed-fraction vs lem-sbc-stalk-normalization-normal-part: global fraction-field statement versus stalk normality.
lem-sbc-integral-closure-algclosed-fraction vs sbc-lem-bc-universal-test: the existing item is a geometric universal counterexample datum; the new node is only the ring-theoretic algebraic-closedness and embedding lemma.
lem-sbc-integral-closure-algclosed-fraction vs lem-sbc-constant-finite-submodule-vanishing: new node concerns integral closures and fraction fields; existing node concerns vanishing of finite constant sheaf submodules.
lem-sbc-integral-closure-algclosed-fraction vs lem-sbc-prime-quotient-detection: new node is a normalization field statement; existing node detects nonzero torsion by prime quotients.
lem-sbc-integral-closure-algclosed-fraction vs lem-sbc-finite-torsion-assemble-prime-powers: new node is ring-theoretic; existing node assembles torsion prime powers.
lem-sbc-integral-closure-algclosed-fraction vs lem-sbc-fg-cyclic-functor-vanishing: new node concerns fraction fields; existing node is a finite-generation vanishing lemma.
lem-sbc-integral-closure-algclosed-fraction vs lem-sbc-finite-torsion-prime-power-step: new node concerns integral closure; existing node concerns torsion induction.
lem-sbc-integral-closure-algclosed-fraction vs lem-sbc-prime-cyclic-detection: new node concerns normalization; existing node detects cyclic prime coefficients.
lem-sbc-integral-closure-algclosed-fraction vs lem-sbc-torsion-constant-prime-devissage: new node concerns algebraically closed fraction fields; existing node is coefficient dévissage.
lem-sbc-integral-closure-algclosed-fraction vs lem-sbc-finite-torsion-prime-power-successor: new node concerns integral closure; existing node is a successor induction.
lem-sbc-integral-closure-algclosed-fraction vs lem-sbc-finite-torsion-extension-induction: new node concerns fraction fields; existing node is an extension induction.
lem-sbc-integral-closure-algclosed-fraction vs lem-kun-0f1d: new node gives normalization algebra; existing node is the cited cohomological theorem.

## Earlier second reading (a previous round; superseded)

- Item statement: checked against Stacks Tags 035H, 035I, 035L and 0F08 and the cited Lean declaration; all hypotheses (affine base, algebraically closed field, integral closure, normal local rings, algebraically closed function field, factorization, and dominance) are present.
- Step 1: checked the affine-spectrum construction against Tag 035H and the affine-spectrum definitions; the induced ring map and integral-closure construction are stated explicitly.
- Step 2: checked the one-factor use of `lem-sbc-integral-closure-finite-normal-product` and the integral-morphism definitions against Tags 035H, 035I, and 035L; the localization, domain, normality, and integrality conclusions match the cited statements.
- Step 3: checked the identification of the function field with `Frac(B)` and the denominator-clearing root argument against Tag 0F08; the argument uses only the new node and the cited function-field and algebraic-closure definitions.
- Step 4: checked contravariant `Spec`, the restriction of the field embedding, factorization, and generic-point dominance against Tags 035I and the cited definitions; injectivity supplies the generic point as claimed.
- New node `lem-sbc-integral-closure-algclosed-fraction`: checked self-contained hypotheses, TeX, definition dependencies, source Tag 0F08, and Mathlib searches; tested the field, zero-kernel, and polynomial-subring cases, with no Mathlib exact match.

Changes made: no mathematical changes were needed after this reading; retained the repaired fraction-field node and the parent steps' explicit algebraic-closure and integral-morphism arguments. The temporary node file is ignored by delivery and does not alter the split.

## Repair of returned delivery

B10/F1/F2: reread `WeilConjectures/SixFunctors/Etale/SmoothBaseChange/CurveTestDatum.lean:126-167` and verified the normalization theorem is complete; the later coefficient theorem at line 198 is independent. The fraction-field prerequisite is now recorded as a Mathlib exact leaf, `IsFractionRing.isAlgClosed_integralClosure`, from `Mathlib/FieldTheory/IsAlgClosed/Basic.lean:149` (project source `WeilConjectures/Mathlib/FieldTheory/IsAlgClosed/Basic.lean:149-165`). E3/E5: step 3 now uses the precise argument supplied by that theorem: a root has a nonzero integral multiple `c*y` in the integral closure, and therefore `y=(c*y)/c`; it no longer asserts the root itself is integral. B5: all Tag 0F08 source fields now identify `literature/stacks-project/etale-cohomology.tex`. B9: the new node records its parent blueprint and `via` chain, group creation metadata, and complete audit/search fields. The search commands were rerun with `msearch.py`; their outputs are in `searches.jsonl`.

## Earlier second reading (a previous round; superseded)

- Item statement: checked against Stacks Tag 0F08 (Lemma 59.88.7) and Tags 035H, 035I, 035L; affine base, algebraically closed field, integral closure, normal local rings, algebraically closed function field, factorization, and dominance agree.
- Step 1: checked against Tag 035H and the affine-spectrum definition; the induced map and integral closure in the image of A are explicit.
- Step 2: checked against Tags 035H, 035I, 035L and the cited finite-product normality node; localization, domain, normality, and integrality match the hypotheses.
- Step 3: checked against Tag 0F08 and `IsFractionRing.isAlgClosed_integralClosure`; the denominator argument uses a nonzero integral multiple of each root and identifies the function field with `Frac(B)`.
- Step 4: checked against Tag 035I and the affine-spectrum/function-field definitions; contravariance gives factorization and injectivity gives generic-point dominance.
- New node `lem-sbc-integral-closure-algclosed-fraction`: statement-only Mathlib leaf with self-contained hypotheses, definition dependencies, Tag 0F08 source, exact declaration/file/line, and recorded searches; tested on a field, a zero-kernel map, and polynomial subrings.

Changes made: no further mathematical changes; retained the repaired fraction-field leaf and explicit parent arguments. Dry-run delivery preflight passed.

## Repair of returned delivery (2026-10-15)

The landing return identified that the parent unit `sk-lem-universal-datum` had no realization fields, even though this split is on its route. I copied the current unit record and filled only its permitted realization fields: statement `sbc-lem-bc-universal-test`, its sole unit proof step carried by `sbc-lem-bc-universal-test`, and `realized_by` pointing to this repair item. I reread the unit statement and all six proof steps of `sbc-lem-bc-universal-test`; the normalization item is used in its third step, while the unit-level key statement carries the complete unit statement and step route. The item and new-node statements, citations, searches, and tool-use declaration are unchanged. The new node remains the exact closed project Mathlib declaration attachment recorded in its audit. The mandated delivery dry run now prints `OK (not pushed)`.

## Second reading by NF

- Item statement: checked clause by clause against Stacks Tag 0F08 (Lemma 59.88.7) and Tags 035H, 035I, 035L; affine base, algebraically closed point field, integral normalization morphism, normal local rings, algebraically closed function field, factorization, and dominance are all present.
- Step 1: checked against Tag 035H and the affine-spectrum definition; the induced map and the integral closure construction are explicit, and the existing integral-closure definition node is now cited.
- Step 2: checked against Tags 035H, 035I, 035L and the existing finite-product integral-closure normality node; the one-factor specialization gives domain and normal localizations, while the integral-closure and integral-morphism definitions justify integrality.
- Step 3: checked against Tag 0F08 and `IsFractionRing.isAlgClosed_integralClosure`; the function field is identified with the fraction field, and the proof uses a nonzero integral multiple of a root before dividing by its image.
- Step 4: checked against Tag 035I and the affine-spectrum/function-field definitions; contravariance gives the factorization, and injectivity makes the zero prime the generic point, hence dominance.
- New node `lem-sbc-integral-closure-algclosed-fraction`: checked as a self-contained statement against Tag 0F08, with all notions defined, TeX and source fields valid, and exact closed Mathlib attachment `IsFractionRing.isAlgClosed_integralClosure` at `Mathlib/FieldTheory/IsAlgClosed/Basic.lean:149`; tested on a field, a polynomial subring, and a zero-kernel map.

Changes made: added the existing integral-closure definition to step 1 and to `citations.json`, since forming the closure was previously uncited; no mathematical statement or proof route changed.
