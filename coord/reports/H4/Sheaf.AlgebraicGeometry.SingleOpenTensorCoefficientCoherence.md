## What changed

Proved `AlgebraicGeometry.single_open_tensor_coefficient_coherence` in
`lean/Sheaf/AlgebraicGeometry/SingleOpenTensorCoefficientCoherence.lean` with its
original signature and visibility. No imports changed. All new helpers are
private proved theorems in the same module.

The proof derives a tensor-coordinate composition equation from the existing
`Scheme.picardTermwiseSingleMap_composition`. Naturality follows directly from
the selected counit and the single-complex comparison. Four applications of the
composition equation, the two given normalization equations, and the existing
`Scheme.Modules.tensorPullbackCompositionIso_associativity` reduce the desired
square to a coefficient identity. A proved generic categorical calculation
cancels only the explicitly invertible final comparison for r.

Updated the existing DAG node's proof and proof origin to describe this actual
argument; its proof dependencies are unchanged. The unit's route is kept.

Change record: `coord/changes/H4-single-open-tensor-proof-environment.md` documents
section-local elaboration attributes and options. No module is adapted.

Repair of reviewer X-2b6a6's H10 return: supplied the exact base-version
`StandardSingleOpenRelativeArrow.lean`, item Lean file, and node JSON below,
including their commit provenance and content hashes. Compiled the unchanged
base downstream source against the delivered item in a fresh `/tmp` sandbox:
both files compile cleanly, in 38.2 and 21.3 seconds, respectively. No Lean or
DAG replacement was requested or made in this repair. The complete snapshots
are embedded in this report so they survive delivery even when the review
clone lacks the original commit. The delivery dry run supplies the axiom and
signature checks.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.single_open_tensor_coefficient_coherence`
(node `lem-pc-single-open-tensor-coefficient-coherence`).

Original holes: 1. Closed: 1. Added: 0. Split off: 0.
No `sorry` remains in the delivered module or is added elsewhere. The private
helpers also have complete proofs. This is a proof, not a decomposition.

## No longer needed

No imports, dependency nodes or modules are removed. Both planned proof
dependencies are used:
`lem-sc-picard-termwise-single-map-composition` and
`lem-pc-tensor-pullback-composition-associativity`.

No additional derived triple-composition associativity lemma, ordinary-pullback
square theorem, flatness hypothesis, or new lower obligation is needed. None of
those were imports or proof dependencies to remove.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface correction was found. The existing two
proof-dependency statements suffice. The normalization and naturality glue is
now proved explicitly, rather than left to another item.

The proof only uses functoriality, naturality and isomorphism cancellation, so
it covers zero modules, empty schemes and identity morphisms. It does not
invert the comparison for q or t and uses no open-immersion hypothesis beyond
the explicit invertibility already present in the statement.


The returned delivery's review clone lacked the base sources and original
commit needed for its signature, node-field and downstream checks. The
following material repairs that H10 reader gate without changing the Lean.

### H10 base provenance and checks

Returned delivery: `2b6a6ab4de73716ca432022f90fb6bca56441d4e`.
Its parent, the base used for all three snapshots:
`60f9cd826daa6302a8d97a7edd6a5537d2ef71ad`.
The snapshots were obtained by read-only Git object reads of that parent;
they are complete source files, including their final newlines. The sandbox's
delivered item and node were checked byte for byte against the returned
delivery. The SHA-256 of the delivered item is
`10db6a43dbd4ec32180683383e7388983dbbec2da84d743c8eca877c2956ad8d`.

The base item and delivered item have identical public theorem signatures,
visibility, docstrings and imports. The declaration comparison reports
`statement_changed = []`, no removed declaration, one original hole closed,
and no new or remaining hole. Comparing the complete base and delivered JSON
objects reports exactly `proof` and `proof_origin` changed; every other field,
including `statement`, `stmt_deps`, `proof_deps` and `lean`, is identical.

The unchanged base downstream file was compiled in
`/tmp/H4-single-open-review-mxfr2ik0`. That sandbox contained only the
unchanged downstream source and the delivered item under `lean/`. The command
below compiles the item first, writes its artifacts to that sandbox's
`.lbuild`, and resolves the downstream import to those artifacts via
`lcompile.py`'s explicit module setup. It does not substitute the shared
library's copy of the item.

```text
python3 /home/ubuntu/weil-launcher/lcompile.py --all /tmp/H4-single-open-review-mxfr2ik0
== Sheaf.AlgebraicGeometry.SingleOpenTensorCoefficientCoherence (compiled)
[38.2 s]
== Sheaf.AlgebraicGeometry.StandardSingleOpenRelativeArrow (compiled)
[21.3 s]
[exit code 0: compiled]
```

Both compiles returned zero with no warnings or errors, within the unchanged
60-second per-file limit. No downstream adaptation was made or delivered.
The `sorry` in the historical base item below is comparison material, not
an added Lean module or a remaining hole of this delivery.

### Reproduce without the original commit

Run this from the delivered repository root after the review report and item
have been provided. It extracts the three embedded snapshots, verifies their
SHA-256 values, writes the unchanged base downstream source and the delivered
item to a fresh `/tmp` sandbox, and runs the same two-file compile. The base
item and node remain available under the temporary sandbox's `base/` directory
for the required signature and field comparisons.

```python
import hashlib
import pathlib
import re
import subprocess
import tempfile

report = pathlib.Path(
    'coord/reports/H4/Sheaf.AlgebraicGeometry.SingleOpenTensorCoefficientCoherence.md'
).read_text()
expected = {
    'lean/Sheaf/AlgebraicGeometry/StandardSingleOpenRelativeArrow.lean':
        '1f612cfc61b7446b29ea1aa76f492a70f77ba63f17a00f2db15fbb4b7764fbcd',
    'lean/Sheaf/AlgebraicGeometry/SingleOpenTensorCoefficientCoherence.lean':
        '08b96c93efd536f6e8ac5cf0816da23d1743361287bee936b02e4847a2dec2b5',
    'dag/nodes/sec-picard-framework/lem-pc-single-open-tensor-coefficient-coherence.json':
        'eaaaf6c42ed0bfb880d474a5d9e9317f9d3e7767ba48c17fcbd5078b61c256d9',
}
tmp = pathlib.Path(tempfile.mkdtemp(prefix='H4-single-open-review-', dir='/tmp'))
pattern = r'^<!-- H4-base-file: ([^\n]+) -->\n```(?:lean|json)\n(.*?)^```\n'
found = dict(re.findall(pattern, report, re.M | re.S))
assert set(found) == set(expected)
for name, digest in expected.items():
    content = found[name].encode()
    assert hashlib.sha256(content).hexdigest() == digest, name
    dest = tmp / 'base' / name
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes(content)
item = 'lean/Sheaf/AlgebraicGeometry/SingleOpenTensorCoefficientCoherence.lean'
downstream = 'lean/Sheaf/AlgebraicGeometry/StandardSingleOpenRelativeArrow.lean'
for name in (item, downstream):
    dest = tmp / name
    dest.parent.mkdir(parents=True, exist_ok=True)
    src = pathlib.Path(item) if name == item else tmp / 'base' / downstream
    dest.write_bytes(src.read_bytes())
subprocess.run(
    ['python3', '/home/ubuntu/weil-launcher/lcompile.py', '--all', str(tmp)],
    check=True,
)
print('Verified base files and compiled unchanged downstream source:', tmp)
```

### Base file: lean/Sheaf/AlgebraicGeometry/StandardSingleOpenRelativeArrow.lean

Git blob: `5b29319125715a5307afabba1a5b6cd8c876d1f8`.
SHA-256: `1f612cfc61b7446b29ea1aa76f492a70f77ba63f17a00f2db15fbb4b7764fbcd`.
Bytes: 13663.

<!-- H4-base-file: lean/Sheaf/AlgebraicGeometry/StandardSingleOpenRelativeArrow.lean -->
```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.AlgebraicGeometry.StandardSingleBaseChangeMap
public import Sheaf.AlgebraicGeometry.RelativeMVMaps
import Sheaf.AlgebraicGeometry.DerivedBaseChangeSourceIso
import Sheaf.AlgebraicGeometry.SingleOpenTensorCoefficientCoherence
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Identifying a relative open arrow for a single coefficient -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem cancel_single_maps
    {A C : Type*} [Category A] [Category C]
    (F : A ⥤ C) {X Y : C} {U V : A} (e : X ⟶ Y) (q : Y ⟶ F.obj U) (b : U ≅ V) :
    (e ≫ q ≫ F.map b.hom) ≫ F.map b.inv = e ≫ q := by
  simp only [Category.assoc, ← F.map_comp, b.hom_inv_id, F.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem single_normalize
    [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : Y.Modules) :
    let := Scheme.Modules.canonicalTensorPullbackAdditive f
    Scheme.picardTermwiseSingleMap f N =
      ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f).app
        ((HomotopyCategory.singleFunctor _ 0).obj N) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex
          (Scheme.Modules.tensorPullback f) (.up ℤ) 0).hom.app N)) := by
  exact cancel_single_maps (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0) _ _
    (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction f)).app N)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem single_open_iso
    [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (N : Y.Modules) :
    IsIso (Scheme.picardTermwiseSingleMap f N) := by
  let : HasDerivedCategory.{u + 1} X.Modules := inferInstanceAs
    (HasDerivedCategory.{u + 1} (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
  let : HasDerivedCategory.{u + 1} Y.Modules := inferInstanceAs
    (HasDerivedCategory.{u + 1} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  let T := Scheme.Modules.tensorPullback f
  let := Scheme.Modules.canonicalTensorPullbackAdditive f
  let η : T ≅ Scheme.Modules.restrictFunctor f :=
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction f) ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback f).symm
  have : PreservesFiniteLimits T := preservesFiniteLimits_of_natIso η.symm
  have : PreservesFiniteColimits T := preservesFiniteColimits_of_natIso η.symm
  let ε := (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f
  let V := HomotopyCategory.quasiIso Y.Modules (.up ℤ)
  have : (DerivedCategory.Qh (C := Y.Modules)).IsLocalization V :=
    inferInstanceAs ((DerivedCategory.Qh (C := Y.Modules)).IsLocalization
      (HomotopyCategory.quasiIso Y.Modules (.up ℤ)))
  have : (derivedPullback f).IsLeftDerivedFunctor ε V :=
    (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) f
  have hInv : V.IsInvertedBy (T.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) := by
    rw [← MorphismProperty.IsInvertedBy.iff_of_iso V T.mapDerivedCategoryFactorsh]
    exact MorphismProperty.IsInvertedBy.of_comp V DerivedCategory.Qh
      (Localization.inverts DerivedCategory.Qh V) T.mapDerivedCategory
  have : IsIso ε :=
    Functor.isIso_of_isLeftDerivedFunctor_of_inverts (derivedPullback f) ε hInv
  rw [single_normalize]
  infer_instance


/-- Restricting a single coefficient to an open contained in its domain gives the
literal tensor-pullback standard comparison, as an isomorphism of arrows.
Source: Stacks Project, Tags 08HY, 0D5S, 01JR and 0A1D.
(blueprint: lem-pc-standard-single-open-relative-arrow).

Proof: The open scheme of W inverse image Z is canonically isomorphic to Z,
with its inclusion into W identified with homOfLE hZ. On the cartesian base
changes use the projection-preserving pullback isomorphism for this scheme
isomorphism and for associating the two pullbacks. Exact open restriction
identifies derived pullback of N[0] with the single complex of the literal tensor
pullback of N; the comparison is the derived-to-ordinary pullback counit. Use
these coefficient comparisons, direct-image composition, and pullback along g
to construct the source and target vertex isomorphisms. Expand relativeMVLocalArrow
and standardSingleBaseChangeMap into their base-change mates and single-complex
counits. The composition law for picardTermwiseSingleMap, the compatibility of
source-isomorphism base-change conjugacy, and the composite-adjunction counit formula
identify the two composites. This is the commuting square defining an arrow
isomorphism; each vertex map is invertible by exact open restriction and scheme
isomorphism transport. More explicitly, put J = W inverse image Z, i:J -> W,
X' = W times_B A with projections q:X' -> W and f':X' -> A, and
J' = X' times_W J with projections r:J' -> X' and k:J' -> J. Let
P = Z times_B A. The source isomorphism e:J -> Z is isoOfLE hZ. The two
projections define e':J' -> P; the inverse is obtained by first lifting into X'
and then into J'. The projection equations and pullback extensionality prove
both inverse identities and k;e = e';(P -> Z).

Write L and R for the pinned derived functors. Let c(h,t) compare successive
pullback along t then h with pullback along h;t.
Put M = tensorPullbackObj (Y.homOfLE hZ) N. Exactness of open restriction,
followed by tensor-pullback composition, gives
alpha:L_e(M[0]) -> L_i(N[0]) as an isomorphism. On J' the same construction
and the equality r;q = k;i give an isomorphism
beta:L_e'((P -> Z tensor-pullback M)[0]) -> L_r((q tensor-pullback N)[0]).
To check the coefficient compatibility required by exists_derivedBaseChange_source_iso,
expand the local coefficient as c(k,i), transport across k;i = r;q, inverse
c(r,q), and L_r(picardTermwiseSingleMap q N). Apply the single-map composition
identity once on each path. The tensor-composition factors are precisely those
used in alpha and beta, so cancellation and naturality give that compatibility.
Apply source-isomorphism conjugacy with these alpha and beta, and invert its
arrow isomorphism to orient it from the local arrow to the standard arrow.
The vertex isomorphisms use the invertible derived adjunction units for e and e';
their inverse identities follow from the adjunction triangle identities.
No assertion about invertibility of a base-change map is used.
Empty Z or W and zero N give the same comparison between zero objects;
Z = W gives the identity-open comparison. -/
theorem standardSingle_open_relative_arrow
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (g : A ⟶ B)
    (W Z : Y.Opens) (hZ : Z ≤ W) (N : W.toScheme.Modules) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let f := W.ι ≫ p
    let K := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) 0).obj N
    let K' := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).obj
        (Scheme.Modules.tensorPullbackObj (pullback.fst f g) N)
    Nonempty
      (relativeMVLocalArrow f (pullback.snd f g) g (pullback.fst f g)
          (IsPullback.of_hasPullback f g) K K'
          (Scheme.picardTermwiseSingleMap (pullback.fst f g) N) (W.ι ⁻¹ᵁ Z) ≅
        Arrow.mk (standardSingleBaseChangeMap (Z.ι ≫ p)
          (Scheme.Modules.tensorPullbackObj (Y.homOfLE hZ) N) g)) := by
  classical
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let f := W.ι ≫ p
  let J := W.ι ⁻¹ᵁ Z
  let q := pullback.fst f g
  let f' := pullback.snd f g
  let r := pullback.fst q J.ι
  let k := pullback.snd q J.ι
  let t := pullback.fst (Z.ι ≫ p) g
  let s := pullback.snd (Z.ι ≫ p) g
  let e := Scheme.Opens.isoOfLE hZ
  have hi : e.hom ≫ Y.homOfLE hZ = J.ι := by
    apply (cancel_mono W.ι).mp
    rw [Category.assoc, Scheme.homOfLE_ι]
    exact Scheme.Opens.isoOfLE_hom_ι hZ
  have hf : e.hom ≫ (Z.ι ≫ p) = J.ι ≫ f := by
    simp only [f, ← Category.assoc, Scheme.Opens.isoOfLE_hom_ι, J, e]
  let e' : pullback q J.ι ≅ pullback (Z.ι ≫ p) g :=
    pullbackSymmetry q J.ι ≪≫ pullbackRightPullbackFstIso f g J.ι ≪≫
      asIso (pullback.map (J.ι ≫ f) g (Z.ι ≫ p) g e.hom (𝟙 _) (𝟙 _)
        (by simpa using hf.symm) (by simp))
  have ht : k ≫ e.hom = e'.hom ≫ t := by
    simp [e', t, k, q]
  have hf' : e'.hom ≫ s = r ≫ f' := by
    simp [e', s, r, f', q]
  let K := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) 0).obj N
  let K' := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).obj
      (Scheme.Modules.tensorPullbackObj q N)
  let M := Scheme.Modules.tensorPullbackObj (Y.homOfLE hZ) N
  let E := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Z.toScheme.toRingedSpace)) 0).obj M
  let E' := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings (pullback (Z.ι ≫ p) g).toRingedSpace)) 0).obj
      (Scheme.Modules.tensorPullbackObj t M)
  let phi0 := (relativeMVComp k J.ι).hom.app K ≫
    eqToHom (congrArg (fun a ↦ (derivedPullback a).obj K)
      (pullback.condition (f := q) (g := J.ι)).symm) ≫
    (relativeMVComp r q).inv.app K ≫
    (derivedPullback r).map (Scheme.picardTermwiseSingleMap q N)
  have : IsOpenImmersion J.ι := inferInstance
  have : IsIso (Scheme.picardTermwiseSingleMap J.ι N) := single_open_iso J.ι N
  have : IsIso (Scheme.picardTermwiseSingleMap e.hom M) := single_open_iso e.hom M
  have : IsIso (Scheme.picardTermwiseSingleMap r
      (Scheme.Modules.tensorPullbackObj q N)) := single_open_iso r _
  have : IsIso (Scheme.picardTermwiseSingleMap e'.hom
      (Scheme.Modules.tensorPullbackObj t M)) := single_open_iso e'.hom _
  let aN := (Scheme.Modules.tensorPullbackCompositionIso
    e.hom (Y.homOfLE hZ) J.ι hi).symm.app N
  have heq : (e'.hom ≫ t) ≫ Y.homOfLE hZ = r ≫ q := by
    rw [← ht, Category.assoc, hi]
    exact (pullback.condition (f := q) (g := J.ι)).symm
  let bN := (Scheme.Modules.tensorPullbackCompositionIso
      e'.hom t (e'.hom ≫ t) rfl).symm.app M ≪≫
    (Scheme.Modules.tensorPullbackCompositionIso
      (e'.hom ≫ t) (Y.homOfLE hZ) (r ≫ q) heq).symm.app N ≪≫
    (Scheme.Modules.tensorPullbackCompositionIso r q (r ≫ q) rfl).app N
  let alpha : (derivedPullback e.hom).obj E ≅ (derivedPullback J.ι).obj K :=
    asIso (Scheme.picardTermwiseSingleMap e.hom M) ≪≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings J.toScheme.toRingedSpace)) 0).mapIso aN ≪≫
      (asIso (Scheme.picardTermwiseSingleMap J.ι N)).symm
  let beta : (derivedPullback e'.hom).obj E' ≅ (derivedPullback r).obj K' :=
    asIso (Scheme.picardTermwiseSingleMap e'.hom (Scheme.Modules.tensorPullbackObj t M)) ≪≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings (pullback q J.ι).toRingedSpace)) 0).mapIso bN ≪≫
      (asIso (Scheme.picardTermwiseSingleMap r (Scheme.Modules.tensorPullbackObj q N))).symm
  have ha : alpha.hom ≫ Scheme.picardTermwiseSingleMap J.ι N =
      Scheme.picardTermwiseSingleMap e.hom M ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings J.toScheme.toRingedSpace)) 0).map aN.hom := by
    simp [alpha]
  have hb : beta.hom ≫
      Scheme.picardTermwiseSingleMap r (Scheme.Modules.tensorPullbackObj q N) =
      Scheme.picardTermwiseSingleMap e'.hom (Scheme.Modules.tensorPullbackObj t M) ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings (pullback q J.ι).toRingedSpace)) 0).map bN.hom := by
    simp [beta]
  have hphi := single_open_tensor_coefficient_coherence
    (Y.homOfLE hZ) q t J.ι r k e e' hi ht
    (pullback.condition (f := q) (g := J.ι)).symm N
    inferInstance alpha.hom beta.hom ha hb
  have h0 : k ≫ (e.hom ≫ (Z.ι ≫ p)) = (e'.hom ≫ s) ≫ g := by
    rw [← Category.assoc, ht, Category.assoc, pullback.condition, ← Category.assoc]
  have transport := exists_derivedBaseChange_source_iso
    (Z.ι ≫ p) s g t pullback.condition e e' k ht h0 E E'
    ((derivedPullback J.ι).obj K) ((derivedPullback r).obj K')
    (Scheme.picardTermwiseSingleMap t M) phi0 alpha beta hphi
  revert transport h0
  rw [hf, hf']
  intro h0 transport
  obtain ⟨a, b, hab⟩ := transport
  exact ⟨(Arrow.isoMk a b hab.symm).symm⟩


end AlgebraicGeometry
```

### Base file: lean/Sheaf/AlgebraicGeometry/SingleOpenTensorCoefficientCoherence.lean

Git blob: `79572734f01b2ca68b89eaa44ecf3f74ee01ac32`.
SHA-256: `08b96c93efd536f6e8ac5cf0816da23d1743361287bee936b02e4847a2dec2b5`.
Bytes: 4832.

<!-- H4-base-file: lean/Sheaf/AlgebraicGeometry/SingleOpenTensorCoefficientCoherence.lean -->
```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import Sheaf.AlgebraicGeometry.RelativeMVMaps
public import Sheaf.AlgebraicGeometry.PicardTermwiseSingleMapComposition
import Sheaf.AlgebraicGeometry.TensorPullbackCompositionAssociativity

/-! # Single-module coefficients in an open square

Source: Stacks Project, Tags 06YJ, 0D5S and 01JR.
(blueprint: lem-pc-single-open-tensor-coefficient-coherence).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Normalized single-module coefficient comparisons commute with an open square.
This is an equality of coefficient maps, before any direct image or base-change mate.
Source: Stacks Project, Tags 06YJ and 0D5S; coefficient calculation in
lem-pc-standard-single-open-relative-arrow.
(blueprint: lem-pc-single-open-tensor-coefficient-coherence).

Proof: Postcompose the desired equality with the invertible single comparison
for r. Substitute the normalization equation for beta on the right. Naturality
moves its tensor-composition factors through the comparison for e'. Apply the
single-map composition identity to (k,i) and (r,q) on the left and to (k,e)
and (e',t) on the right. Substitute the normalization equation for alpha.
The tensor-composition associativity identity for (k,e,z), together with
hi and ht, identifies the coefficient factors on the two sides; the path
(e',t,z) is the same triple composite by ht, and hsq identifies it with (r,q).
Equality induction on hi, ht and hsq identifies the transports. Reassociate,
cancel the derived composition isomorphisms, and cancel the final comparison
for r. No single comparison for q or t is inverted. This is valid for zero
modules, empty schemes, and identity morphisms. The statement does not require
open immersions: the invertibility needed for cancellation is explicit. -/
theorem single_open_tensor_coefficient_coherence
    {W Z X' P J J' : Scheme.{u}}
    (z : Z ⟶ W) (q : X' ⟶ W) (t : P ⟶ Z)
    (i : J ⟶ W) (r : J' ⟶ X') (k : J' ⟶ J)
    (e : J ≅ Z) (e' : J' ≅ P)
    (hi : e.hom ≫ z = i) (ht : k ≫ e.hom = e'.hom ≫ t)
    (hsq : k ≫ i = r ≫ q) (N : W.Modules) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let K := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings W.toRingedSpace)) 0).obj N
    let M := Scheme.Modules.tensorPullbackObj z N
    let E := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj M
    let E' := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings P.toRingedSpace)) 0).obj
        (Scheme.Modules.tensorPullbackObj t M)
    let K' := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
        (Scheme.Modules.tensorPullbackObj q N)
    let phi0 := (relativeMVComp k i).hom.app K ≫
      eqToHom (congrArg (fun a ↦ (derivedPullback a).obj K) hsq) ≫
      (relativeMVComp r q).inv.app K ≫
      (derivedPullback r).map (Scheme.picardTermwiseSingleMap q N)
    let aN := (Scheme.Modules.tensorPullbackCompositionIso e.hom z i hi).symm.app N
    let heq : (e'.hom ≫ t) ≫ z = r ≫ q := by
      rw [← ht, Category.assoc, hi, hsq]
    let bN := (Scheme.Modules.tensorPullbackCompositionIso
        e'.hom t (e'.hom ≫ t) rfl).symm.app M ≪≫
      (Scheme.Modules.tensorPullbackCompositionIso
        (e'.hom ≫ t) z (r ≫ q) heq).symm.app N ≪≫
      (Scheme.Modules.tensorPullbackCompositionIso r q (r ≫ q) rfl).app N
    IsIso (Scheme.picardTermwiseSingleMap r (Scheme.Modules.tensorPullbackObj q N)) →
    ∀ (alpha : (derivedPullback e.hom).obj E ⟶ (derivedPullback i).obj K)
      (beta : (derivedPullback e'.hom).obj E' ⟶ (derivedPullback r).obj K'),
      alpha ≫ Scheme.picardTermwiseSingleMap i N =
        Scheme.picardTermwiseSingleMap e.hom M ≫
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings J.toRingedSpace)) 0).map aN.hom →
      beta ≫ Scheme.picardTermwiseSingleMap r (Scheme.Modules.tensorPullbackObj q N) =
        Scheme.picardTermwiseSingleMap e'.hom (Scheme.Modules.tensorPullbackObj t M) ≫
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings J'.toRingedSpace)) 0).map bN.hom →
      (derivedPullback k).map alpha ≫ phi0 =
        (relativeMVComp k e.hom).hom.app E ≫
        eqToHom (congrArg (fun a ↦ (derivedPullback a).obj E) ht) ≫
        (relativeMVComp e'.hom t).inv.app E ≫
        (derivedPullback e'.hom).map (Scheme.picardTermwiseSingleMap t M) ≫
        beta := by sorry

end AlgebraicGeometry
```

### Base file: dag/nodes/sec-picard-framework/lem-pc-single-open-tensor-coefficient-coherence.json

Git blob: `ce68db62409f373fe6460d1b23c93744cdae8ff1`.
SHA-256: `eaaaf6c42ed0bfb880d474a5d9e9317f9d3e7767ba48c17fcbd5078b61c256d9`.
Bytes: 8822.

<!-- H4-base-file: dag/nodes/sec-picard-framework/lem-pc-single-open-tensor-coefficient-coherence.json -->
```json
{
 "id": "lem-pc-single-open-tensor-coefficient-coherence",
 "kind": "statement",
 "title": "Normalized single tensor coefficient comparisons respect a coordinate square",
 "statement": "Use standard derived categories [def-pc-derived-category] and the pinned single tensor comparison Q_a [lem-sc-picard-termwise-single-map-composition]. Let z:Z→W, q:X′→W, t:P→Z, i:J→W, r:J′→X′ and k:J′→J be scheme maps, with e:J≅Z and e′:J′≅P, and equalities e;z=i, k;e=e′;t, k;i=r;q. Let N be an O_W-module, M=T_z N, E=M[0], E′=(T_t M)[0], K=N[0], K′=(T_q N)[0], with literal tensor pullback [def-pc-module-pullback]. Write c for relativeMVComp [def-pc-relative-mv-maps] and C(a,b,d) for tensorPullbackCompositionIso from T_d to T_a T_b [def-pc-tensor-pullback-composition-iso]. Set aN=C(e,z,i)⁻¹(N) and bN=C(e′,t,e′;t)⁻¹(M);C(e′;t,z,r;q)⁻¹(N);C(r,q,r;q)(N), using the displayed equalities. Suppose Q_r(T_q N) is invertible. For any alpha:L_e E→L_i K and beta:L_e′ E′→L_r K′ with alpha;Q_i(N)=Q_e(M);aN[0] and beta;Q_r(T_q N)=Q_e′(T_t M);bN[0], one has L_k(alpha);(c(k,i);transport(k;i=r;q);c(r,q)⁻¹;L_r(Q_q(N)))=c(k,e);transport(k;e=e′;t);c(e′,t)⁻¹;L_e′(Q_t(M));beta. This is solely a coefficient identity, with no direct image, base scheme or base-change mate.",
 "stmt_deps": [
  "def-pc-derived-category",
  "def-pc-module-pullback",
  "def-pc-relative-mv-maps",
  "def-pc-tensor-pullback-composition-iso",
  "lem-sc-picard-termwise-single-map-composition"
 ],
 "source": {
  "document": "Stacks Project",
  "place": "Tags 06YJ and 0D5S; coefficient normalization calculation of lem-pc-standard-single-open-relative-arrow, before taking direct image."
 },
 "proof": [
  {
   "text": "Postcompose with picardTermwiseSingleMap r (T_q N), which is invertible by the explicit hypothesis. Substitute the normalization equation for beta. Apply picardTermwiseSingleMap_composition to (r,q) and (k,i), expressing successive single comparisons using the selected derived and tensor composition maps. Substitute the normalization equation for alpha; naturality of the selected derived counit and the chain single comparison moves the single image of aN across the k comparison.",
   "uses": [
    "lem-sc-picard-termwise-single-map-composition"
   ],
   "elementary": false
  },
  {
   "text": "Apply the same single-comparison composition formula to (k,e.hom) and (e'.hom,t). The tensor composition factors on the two routes agree by tensorPullbackCompositionIso_associativity for (k,e.hom,z), and transport along ht identifies k;e with e';t. The equalities hi and hsq identify the total composite with r;q. Equality induction identifies the transports. The three factors defining bN are exactly the inverse composition factors followed by the r;q tensor composition. Reassociate, cancel the inverse derived composition factors, and cancel the postcomposed invertible r comparison. No single comparison for q or t is inverted.",
   "uses": [
    "lem-sc-picard-termwise-single-map-composition",
    "lem-pc-tensor-pullback-composition-associativity"
   ],
   "elementary": false
  }
 ],
 "proof_deps": [
  "lem-pc-tensor-pullback-composition-associativity",
  "lem-sc-picard-termwise-single-map-composition"
 ],
 "proof_origin": {
  "by": "agent",
  "document": "Stacks Project",
  "place": "Tags 06YJ and 0D5S; coefficient normalization calculation of lem-pc-standard-single-open-relative-arrow, before taking direct image."
 },
 "mathlib_searches": [
  {
   "tool": "leansearch",
   "query": "Single complex pullback comparisons commute with an open immersion square and source isomorphisms",
   "results": "Service unavailable: Internal Server Error.",
   "date": "2026-10-14",
   "verdict": "unavailable"
  },
  {
   "tool": "loogle",
   "query": "CategoryTheory.Functor.isIso_of_isLeftDerivedFunctor_of_inverts",
   "results": "One hit, the generic derived-counit invertibility theorem. It is used in the proved open comparison helper, not a match for this coefficient equation.",
   "date": "2026-10-14",
   "verdict": "generic tool only"
  },
  {
   "tool": "grep",
   "query": "singleMapHomologicalComplex|isIso_of_isLeftDerivedFunctor_of_inverts",
   "results": "11 hits including homotopy single comparison, derived ExactFunctor and generic derived-counit invertibility. Local rg also found the proved canonicalSinglePullbackSquare for ordinary coefficients, and tensor composition associativity. None states this literal-tensor coordinate equation.",
   "date": "2026-10-14",
   "verdict": "generic tools and related ordinary coefficient equation only"
  }
 ],
 "mathlib_match": null,
 "status": "split",
 "merged_into": null,
 "created": {
  "by": "worker",
  "item": "Sheaf.AlgebraicGeometry.StandardSingleOpenRelativeArrow",
  "date": "2026-10-14",
  "group": "V4"
 },
 "blueprint": {
  "is": null,
  "from": {
   "node": "lem-pc-coherent-hi",
   "place": "Tags 06YJ and 0D5S; coefficient normalization calculation of lem-pc-standard-single-open-relative-arrow, before taking direct image.",
   "via": [
    "lem-pc-standard-single-open-relative-arrow"
   ]
  },
  "same_as": []
 },
 "chapter": "sec-picard-framework",
 "unit": "sk-thm-picard-coherence",
 "lean": {
  "existing": false,
  "module": "Sheaf.AlgebraicGeometry.SingleOpenTensorCoefficientCoherence",
  "file": "lean/Sheaf/AlgebraicGeometry/SingleOpenTensorCoefficientCoherence.lean",
  "declaration": "AlgebraicGeometry.single_open_tensor_coefficient_coherence",
  "statement": "theorem single_open_tensor_coefficient_coherence {W Z X' P J J' : Scheme.{u}} (z : Z ⟶ W) (q : X' ⟶ W) (t : P ⟶ Z) (i : J ⟶ W) (r : J' ⟶ X') (k : J' ⟶ J) (e : J ≅ Z) (e' : J' ≅ P) (hi : e.hom ≫ z = i) (ht : k ≫ e.hom = e'.hom ≫ t) (hsq : k ≫ i = r ≫ q) (N : W.Modules) : letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings X.toRingedSpace)) let K := (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings W.toRingedSpace)) 0).obj N let M := Scheme.Modules.tensorPullbackObj z N let E := (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj M let E' := (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings P.toRingedSpace)) 0).obj (Scheme.Modules.tensorPullbackObj t M) let K' := (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj (Scheme.Modules.tensorPullbackObj q N) let phi0 := (relativeMVComp k i).hom.app K ≫ eqToHom (congrArg (fun a ↦ (derivedPullback a).obj K) hsq) ≫ (relativeMVComp r q).inv.app K ≫ (derivedPullback r).map (Scheme.picardTermwiseSingleMap q N) let aN := (Scheme.Modules.tensorPullbackCompositionIso e.hom z i hi).symm.app N let heq : (e'.hom ≫ t) ≫ z = r ≫ q := by rw [← ht, Category.assoc, hi, hsq] let bN := (Scheme.Modules.tensorPullbackCompositionIso e'.hom t (e'.hom ≫ t) rfl).symm.app M ≪≫ (Scheme.Modules.tensorPullbackCompositionIso (e'.hom ≫ t) z (r ≫ q) heq).symm.app N ≪≫ (Scheme.Modules.tensorPullbackCompositionIso r q (r ≫ q) rfl).app N IsIso (Scheme.picardTermwiseSingleMap r (Scheme.Modules.tensorPullbackObj q N)) → ∀ (alpha : (derivedPullback e.hom).obj E ⟶ (derivedPullback i).obj K) (beta : (derivedPullback e'.hom).obj E' ⟶ (derivedPullback r).obj K'), alpha ≫ Scheme.picardTermwiseSingleMap i N = Scheme.picardTermwiseSingleMap e.hom M ≫ (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings J.toRingedSpace)) 0).map aN.hom → beta ≫ Scheme.picardTermwiseSingleMap r (Scheme.Modules.tensorPullbackObj q N) = Scheme.picardTermwiseSingleMap e'.hom (Scheme.Modules.tensorPullbackObj t M) ≫ (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings J'.toRingedSpace)) 0).map bN.hom → (derivedPullback k).map alpha ≫ phi0 = (relativeMVComp k e.hom).hom.app E ≫ eqToHom (congrArg (fun a ↦ (derivedPullback a).obj E) ht) ≫ (relativeMVComp e'.hom t).inv.app E ≫ (derivedPullback e'.hom).map (Scheme.picardTermwiseSingleMap t M) ≫ beta",
  "branch": "sheaf-dag",
  "by": "V4",
  "date": "2026-10-14"
 },
 "reviewed": {
  "date": "2026-10-14",
  "by": "L",
  "reviewer": "COMPILER",
  "group": "V4",
  "result": "pass",
  "landing": "20261014T034914-L-816221",
  "kind": "interface",
  "note": "new node of a stage-3 delivery, read against its source by the reviewer"
 },
 "reviewed_proof": {
  "date": "2026-10-14",
  "by": "L",
  "reviewer": "COMPILER",
  "group": "V4",
  "result": "pass",
  "landing": "20261014T034914-L-816221",
  "kind": "interface",
  "note": "AUTO: proofs only; landed in a batch after the tools' static checks; compiled with the probe by the group's delivery tool, verified by the global build (compile, axioms, sorry, 60 s per file); not read by a reviewer (stage 3, decision of the human 2026-10-12)"
 }
}
```

## Earlier second reading (a previous round; superseded)

1. Compared the delivered module with the repository version: the public theorem signature and visibility are byte for byte unchanged; the proof-only additions are confined to private helpers and local attributes. Verdict: pass.

2. Compiled the module with `lcompile.py`; it succeeds in about 37 seconds. Searched for forbidden constructs and remaining `sorry`; none occur in the delivered Lean module. The public theorem uses only the permitted dependencies and its proof has no new holes. Verdict: pass.

3. Checked the existing statement and the private helper statements against the planned coefficient calculation. The helper identities are proved categorical equalities, with no weakened hypotheses or altered conclusions, and no split-off statements were added. Verdict: pass.

4. Checked the proof route and imports against the DAG. Both planned proof dependencies are used, no import is removable, and the unit route remains intact. Verdict: pass.

5. Compared the changed DAG node with the Lean proof: its three proof steps, dependencies, and proof origin describe the normalization, associativity, and final cancellation actually used. Verdict: pass.

Changed only the report to record this second reading; no Lean or DAG repair was needed.


## Second reading by H4

1. **Interface and visibility — pass.** Read the complete repository and delivered
   modules and their diff. The existing public declaration
   `AlgebraicGeometry.single_open_tensor_coefficient_coherence` has byte-identical
   statement, visibility and docstring. All three imports are identical. The only
   new declarations are ten private proved theorems; no definition is changed.
   The elaboration options and reducibility attributes end with the helper
   section before the public theorem, as the change record states. Compared all
   three embedded H10 baseline snapshots with the current repository: each is
   byte-identical, and its byte count and SHA-256 match the manifest.

2. **Proof and axioms — pass.** Compiled a scratch copy of the delivered item,
   appending explicit `#print axioms` checks for the public theorem and all ten
   private helpers. It compiled without warnings or errors in 37.0 seconds.
   Every printed axiom set is contained in `propext`, `Classical.choice`, and
   `Quot.sound`; none contains `sorryAx`. A lexical check found no `sorry`,
   `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` in the delivered
   module. Then compiled the unchanged embedded base source of
   `StandardSingleOpenRelativeArrow.lean` against the scratch item's own compiled
   artifacts, using `lcompile.py --all` on
   `scratchpad/second-reading`: it compiled cleanly in 20.4 seconds. This
   independently satisfies the H10 return's downstream reader gate. Neither
   baseline source nor scratch axiom checks are delivered as Lean modules.

3. **Split statements and mathematical strength — pass.** No new public statement
   or split-off hole exists. Read every private helper: normalization cancels
   the unique-adjoint isomorphism with its inverse; counit normalization removes
   identity comparison components; naturality composes the selected counit's
   naturality with that of the single-complex comparison; the composition helper
   postcomposes the existing composition theorem with the single comparison.
   The generic square calculation cancels only its assumed monomorphism and
   explicitly supplied isomorphisms. The final proof supplies the monomorphism
   from the original `IsIso` hypothesis for the r comparison. No invertibility
   of q or t, flatness, or open-immersion hypothesis is introduced. Identity
   morphisms, zero coefficients, and empty schemes obey these categorical
   equations without an excluded case. No data is constructed from a new
   existence assertion.

4. **Shortest route, imports, and unit — pass.** Read both dependency statements
   and checked all four applications of
   `Scheme.picardTermwiseSingleMap_composition` and the application of
   `Scheme.Modules.tensorPullbackCompositionIso_associativity`. Fresh searches
   with `msearch.py` (LeanFinder, Loogle, and grep), using naturality and
   single-coordinate terminology, found general naturality and single-functor
   tools already used by the proof, but no replacement for this normalized
   coefficient square. Local searches also found
   `Scheme.Modules.canonicalSinglePullbackSquare`: it uses ordinary pullback
   coordinates and would require additional transport, so it does not shorten
   this literal-tensor proof. Both public imports supply names in the original
   statement (`relativeMVComp` and `picardTermwiseSingleMap`); tensor associativity
   is needed only for the proof and remains a plain import. Both old
   `proof_deps` are used, so `## No longer needed` is complete with none removed.
   Read `dag/units/sk-thm-picard-coherence.json`: its statement and step route,
   and its existing empty `realized` entries, are unmodified. This proof closes
   the same subordinate coefficient calculation; no unit step is bypassed.
   The recorded literature `_section.md` is absent on this machine; the unit
   record includes its statement and complete proof text.

5. **DAG agreement — pass.** Compared the complete JSON objects: only `proof` and
   `proof_origin` differ. `statement`, `stmt_deps`, `proof_deps`, `lean`, `chapter`,
   `unit`, and all other fields are unchanged. The three recorded steps match
   the code: tensor normalization/naturality/composition; the inverted tensor
   associativity equation defining `hcoef`; and four composition equations,
   the alpha/beta normalization hypotheses, and final r cancellation through
   `normalized_square_algebra`. There are no new nodes to audit.

Changed only this report to record the independent second reading and fresh
H10 verification. No Lean, node, import, or change-record repair was necessary.
One original hole is closed, zero holes are added, zero are split off, and no
module is pruned.
