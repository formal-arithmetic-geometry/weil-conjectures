## What changed

Removed Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime entirely from
Sheaf.RingTheory.ZariskisMainAway, completing the requested wrapper removal.
The module remains as compatibility imports. Its three callers now convert the
open fibre singleton directly with Mathlib and apply the existing Mathlib
Zariski-main theorem. All caller signatures and visibility remain identical.
Updated the Zariski-main DAG proof and Lean-record explanation to match.
Change record: coord/changes/zariskisMainProperty-wrapper-retirement.md.

## Proved and sorry left

Zero original holes, zero holes closed, zero holes added, zero split off.
The removed declaration was already proved. This is an interface repair and
pruning, not new proof progress. The retained proofs
Algebra.exists_finite_subalgebra_away_of_isQuasiFiniteAtPrime,
Algebra.ringKrullDim_le_of_isQuasiFiniteAtPrime, and
AlgebraicGeometry.integralClosure_finiteFibrePart_localization compile.
No sorry occurs in any delivered module, including the private neighborhood lemma.

## No longer needed

The three adapted callers no longer import Sheaf.RingTheory.ZariskisMainAway.
That module no longer imports Mathlib.RingTheory.ZariskisMainTheorem.
The removed Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime is no longer needed.
The node lem-weil-pbc-integral-closure-zariski-main-away stays, realized directly
by Mathlib's Algebra.ZariskisMainProperty.of_finiteType. No mathematical node is
pruned: the fibre-hypothesis conversion and Zariski-main step remain in each proof.
Sheaf.RingTheory.QuasiFiniteIntegralClosureOpen still has an unused private import
of the retired compatibility module; this delivery cannot remove it under the
forced-adaptation rule because that original module still compiles unchanged.

## Where the brief, the DAG or earlier work was wrong

The assigned module already had zero sorry. K2 had repaired the localization
conclusion by retaining a conversion-only helper under the old name; the upstream
request was to remove the wrapper and re-point its callers. This delivery finishes
that removal rather than reporting the assignment as stale.
The scheme-predicate duplication mentioned in the same repair line belongs to
Sheaf.AlgebraicGeometry.QuasiFiniteMorphism, not this held module. Its definitions
are unchanged: removing this ring wrapper forces no change to their interfaces,
so the forced-adaptation exception does not authorize editing that module.

## Forced adaptations

Each original caller below fails against the removed theorem. In
Sheaf.RingTheory.QuasiFiniteAtFiniteSubalgebraAway, replace original line 56
with the local QuasiFiniteAt instance proof. In
Sheaf.RingTheory.QuasiFiniteLocalDimension, replace original line 53 with
the same conversion. In
Sheaf.Paper.IntegralClosureFiniteFibrePartLocalization, replace original line
129 with the local conversion for p and its hypothesis hqf p hp. In all three,
remove only the obsolete private import of Sheaf.RingTheory.ZariskisMainAway.
The replacement proofs transport the original hypothesis; no other proof steps,
signatures or visibility change. All adapted modules compile. Exact counterfactual
errors follow.

### Sheaf.Paper.IntegralClosureFiniteFibrePartLocalization
Original against changed dependencies failed:
```
/tmp/forced-adaptation-910lc7xq/lean/Sheaf/Paper/IntegralClosureFiniteFibrePartLocalization.lean:129:14: error(lean.unknownIdentifier): Unknown constant `Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime`
/tmp/forced-adaptation-910lc7xq/lean/Sheaf/Paper/IntegralClosureFiniteFibrePartLocalization.lean:127:79: error: unsolved goals
A : Type u
B : Type v
inst✝⁸ : CommRing A
inst✝⁷ : CommRing B
inst✝⁶ : Algebra A B
inst✝⁵ : Algebra.FiniteType A B
I : Ideal A
C₁ : Type w
C₂ : Type z
inst✝⁴ : CommRing C₁
inst✝³ : CommRing C₂
inst✝² : Algebra (A ⧸ I) C₁
inst✝¹ : Algebra (A ⧸ I) C₂
inst✝ : Module.Finite (A ⧸ I) C₁
e : B ⧸ Ideal.map (algebraMap A B) I ≃+* C₁ × C₂
he :
  ∀ (a : A),
    e ((Ideal.Quotient.mk (Ideal.map (algebraMap A B) I)) ((algebraMap A B) a)) =
      ((algebraMap (A ⧸ I) C₁) ((Ideal.Quotient.mk I) a), (algebraMap (A ⧸ I) C₂) ((Ideal.Quotient.mk I) a))
ε : B ⧸ Ideal.map (algebraMap A B) I
hε : e ε = (1, 0)
hcompat :
  ∀ (a : A),
    (algebraMap (A ⧸ I) C₁) ((Ideal.Quotient.mk I) a) =
      (e ((Ideal.Quotient.mk (Ideal.map (algebraMap A B) I)) ((algebraMap A B) a))).1
π : B →+* B ⧸ Ideal.map (algebraMap A B) I := Ideal.Quotient.mk (Ideal.map (algebraMap A B) I)
π' : ↥(integralClosure A B) →+* ↥(integralClosure A B) ⧸ Ideal.map (algebraMap A ↥(integralClosure A B)) I :=
  Ideal.Quotient.mk (Ideal.map (algebraMap A ↥(integralClosure A B)) I)
ι : ↥(integralClosure A B) →+* B := algebraMap (↥(integralClosure A B)) B
β : B →+* C₁ := (RingHom.fst C₁ C₂).comp (e.toRingHom.comp π)
T : Set (PrimeSpectrum B) := Set.range (PrimeSpectrum.comap β)
hqf :
  have π := (RingHom.fst C₁ C₂).comp (e.toRingHom.comp (Ideal.Quotient.mk (Ideal.map (algebraMap A B) I)));
  have T := Set.range (PrimeSpectrum.comap π);
  ∀ q ∈ T, Algebra.IsQuasiFiniteAtPrime A B q
p : PrimeSpectrum B
hp : p ∈ T
⊢ ∃ r, ι r ∉ p.asIdeal ∧ Function.Bijective ⇑(Localization.awayMap ι r)

(with the modules compiled into /tmp/forced-adaptation-910lc7xq/.lbuild) [5.1 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.RingTheory.QuasiFiniteAtFiniteSubalgebraAway
Original against changed dependencies failed:
```
/tmp/forced-adaptation-z5og2v20/lean/Sheaf/RingTheory/QuasiFiniteAtFiniteSubalgebraAway.lean:56:12: error(lean.unknownIdentifier): Unknown identifier `zariskisMainProperty_of_isQuasiFiniteAtPrime`
/tmp/forced-adaptation-z5og2v20/lean/Sheaf/RingTheory/QuasiFiniteAtFiniteSubalgebraAway.lean:55:72: error: unsolved goals
R : Type u
S : Type v
inst✝³ : CommRing R
inst✝² : CommRing S
inst✝¹ : Algebra R S
inst✝ : FiniteType R S
q : PrimeSpectrum S
hq : IsQuasiFiniteAtPrime R S q
⊢ ∃ S', Module.Finite R ↥S' ∧ ∃ g, ↑g ∉ q.asIdeal ∧ Function.Bijective ⇑(Localization.awayMap S'.val.toRingHom g)

(with the modules compiled into /tmp/forced-adaptation-z5og2v20/.lbuild) [1.7 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.RingTheory.QuasiFiniteLocalDimension
Original against changed dependencies failed:
```
/tmp/forced-adaptation-zc14coqs/lean/Sheaf/RingTheory/QuasiFiniteLocalDimension.lean:53:12: error(lean.unknownIdentifier): Unknown identifier `zariskisMainProperty_of_isQuasiFiniteAtPrime`
/tmp/forced-adaptation-zc14coqs/lean/Sheaf/RingTheory/QuasiFiniteLocalDimension.lean:50:80: error: unsolved goals
R : Type u
S : Type v
inst✝³ : CommRing R
inst✝² : CommRing S
inst✝¹ : Algebra R S
inst✝ : FiniteType R S
q : PrimeSpectrum S
hq : IsQuasiFiniteAtPrime R S q
T : Subalgebra R S := integralClosure R S
q' : Ideal ↥T := Ideal.under (↥T) q.asIdeal
⊢ ringKrullDim (Localization.AtPrime q.asIdeal) ≤
    ringKrullDim (Localization.AtPrime (PrimeSpectrum.comap (algebraMap R S) q).asIdeal)

(with the modules compiled into /tmp/forced-adaptation-zc14coqs/.lbuild) [1.6 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Second reading by Y3

1. Compared every delivered Lean module and the node against the repository with
   `diff -u`. PASS: all retained declaration signatures and visibility are byte
   for byte unchanged. The sole interface change is the expressly recorded
   retirement of Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime. Only the
   three failing conversion lines and their obsolete private imports are adapted;
   no definition or target statement changes. The change record accounts for all
   three users and the untouched fourth importer.
2. Independently compiled all four files through lcompile.py --all. PASS: no
   errors or warnings; no sorry, forbidden declaration or hollow definition.
   Scratch copies with #print axioms for all three retained public theorems
   report exactly propext, Classical.choice and Quot.sound. The compatibility
   module has no declarations; the private neighborhood proof is unchanged.
3. PASS: no split-off statements, new declarations or new nodes. There are zero
   original holes, zero closed holes and zero added holes. This is a wrapper
   retirement/interface repair, with no claimed proof progress.
4. Read the complete delivered proofs and Mathlib's ZariskisMainProperty
   definition, of_finiteType and QuasiFiniteAt.of_isOpen_singleton_fiber. PASS:
   the shortest direct Mathlib route is retained, with the defining open singleton
   transported through the same fibre homeomorphism. The proof-only Zariski-main
   imports in callers remain private. No old proof dependency is removed; the
   obsolete wrapper imports are all listed under No longer needed. Read
   dag/units/sk-thm-p1.json: its realized statement and steps are unaffected, and
   the Zariski-main step remains in each caller. The still-importing fourth module
   is correctly excluded because its adaptation would not be forced.
5. PASS: node statement and dependencies are unchanged; proof, proof_deps,
   proof_origin and lean record describe the local fibre conversion followed by
   Mathlib's theorem, whose definition gives exactly the node's localization
   conclusion. No new-node field requirements apply.

Second reading changed only this report: added the independent review and
compilation/axiom evidence. No Lean or node repair was needed.

## Forced adaptations

### Sheaf.Paper.IntegralClosureFiniteFibrePartLocalization
Original against changed dependencies failed:
```
/tmp/forced-adaptation-ogpu0tk1/lean/Sheaf/Paper/IntegralClosureFiniteFibrePartLocalization.lean:129:14: error(lean.unknownIdentifier): Unknown constant `Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime`
/tmp/forced-adaptation-ogpu0tk1/lean/Sheaf/Paper/IntegralClosureFiniteFibrePartLocalization.lean:127:79: error: unsolved goals
A : Type u
B : Type v
inst✝⁸ : CommRing A
inst✝⁷ : CommRing B
inst✝⁶ : Algebra A B
inst✝⁵ : Algebra.FiniteType A B
I : Ideal A
C₁ : Type w
C₂ : Type z
inst✝⁴ : CommRing C₁
inst✝³ : CommRing C₂
inst✝² : Algebra (A ⧸ I) C₁
inst✝¹ : Algebra (A ⧸ I) C₂
inst✝ : Module.Finite (A ⧸ I) C₁
e : B ⧸ Ideal.map (algebraMap A B) I ≃+* C₁ × C₂
he :
  ∀ (a : A),
    e ((Ideal.Quotient.mk (Ideal.map (algebraMap A B) I)) ((algebraMap A B) a)) =
      ((algebraMap (A ⧸ I) C₁) ((Ideal.Quotient.mk I) a), (algebraMap (A ⧸ I) C₂) ((Ideal.Quotient.mk I) a))
ε : B ⧸ Ideal.map (algebraMap A B) I
hε : e ε = (1, 0)
hcompat :
  ∀ (a : A),
    (algebraMap (A ⧸ I) C₁) ((Ideal.Quotient.mk I) a) =
      (e ((Ideal.Quotient.mk (Ideal.map (algebraMap A B) I)) ((algebraMap A B) a))).1
π : B →+* B ⧸ Ideal.map (algebraMap A B) I := Ideal.Quotient.mk (Ideal.map (algebraMap A B) I)
π' : ↥(integralClosure A B) →+* ↥(integralClosure A B) ⧸ Ideal.map (algebraMap A ↥(integralClosure A B)) I :=
  Ideal.Quotient.mk (Ideal.map (algebraMap A ↥(integralClosure A B)) I)
ι : ↥(integralClosure A B) →+* B := algebraMap (↥(integralClosure A B)) B
β : B →+* C₁ := (RingHom.fst C₁ C₂).comp (e.toRingHom.comp π)
T : Set (PrimeSpectrum B) := Set.range (PrimeSpectrum.comap β)
hqf :
  have π := (RingHom.fst C₁ C₂).comp (e.toRingHom.comp (Ideal.Quotient.mk (Ideal.map (algebraMap A B) I)));
  have T := Set.range (PrimeSpectrum.comap π);
  ∀ q ∈ T, Algebra.IsQuasiFiniteAtPrime A B q
p : PrimeSpectrum B
hp : p ∈ T
⊢ ∃ r, ι r ∉ p.asIdeal ∧ Function.Bijective ⇑(Localization.awayMap ι r)

(with the modules compiled into /tmp/forced-adaptation-ogpu0tk1/.lbuild) [5.7 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.RingTheory.QuasiFiniteAtFiniteSubalgebraAway
Original against changed dependencies failed:
```
/tmp/forced-adaptation-ylvbip6k/lean/Sheaf/RingTheory/QuasiFiniteAtFiniteSubalgebraAway.lean:56:12: error(lean.unknownIdentifier): Unknown identifier `zariskisMainProperty_of_isQuasiFiniteAtPrime`
/tmp/forced-adaptation-ylvbip6k/lean/Sheaf/RingTheory/QuasiFiniteAtFiniteSubalgebraAway.lean:55:72: error: unsolved goals
R : Type u
S : Type v
inst✝³ : CommRing R
inst✝² : CommRing S
inst✝¹ : Algebra R S
inst✝ : FiniteType R S
q : PrimeSpectrum S
hq : IsQuasiFiniteAtPrime R S q
⊢ ∃ S', Module.Finite R ↥S' ∧ ∃ g, ↑g ∉ q.asIdeal ∧ Function.Bijective ⇑(Localization.awayMap S'.val.toRingHom g)

(with the modules compiled into /tmp/forced-adaptation-ylvbip6k/.lbuild) [1.8 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.RingTheory.QuasiFiniteLocalDimension
Original against changed dependencies failed:
```
/tmp/forced-adaptation-ht1z6p5q/lean/Sheaf/RingTheory/QuasiFiniteLocalDimension.lean:53:12: error(lean.unknownIdentifier): Unknown identifier `zariskisMainProperty_of_isQuasiFiniteAtPrime`
/tmp/forced-adaptation-ht1z6p5q/lean/Sheaf/RingTheory/QuasiFiniteLocalDimension.lean:50:80: error: unsolved goals
R : Type u
S : Type v
inst✝³ : CommRing R
inst✝² : CommRing S
inst✝¹ : Algebra R S
inst✝ : FiniteType R S
q : PrimeSpectrum S
hq : IsQuasiFiniteAtPrime R S q
T : Subalgebra R S := integralClosure R S
q' : Ideal ↥T := Ideal.under (↥T) q.asIdeal
⊢ ringKrullDim (Localization.AtPrime q.asIdeal) ≤
    ringKrullDim (Localization.AtPrime (PrimeSpectrum.comap (algebraMap R S) q).asIdeal)

(with the modules compiled into /tmp/forced-adaptation-ht1z6p5q/.lbuild) [1.6 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
