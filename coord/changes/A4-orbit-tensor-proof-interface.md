# Orbit tensor proof interface

## Reason

Extract the seven existing section constructions into a base module so that the two
proper proof steps and the proved local-frame theorem can depend on them without an
import cycle. Reexport that base publicly from the original module. The declarations,
universes, data bodies and resulting theorem statement are unchanged. No existing
module other than the assigned item changes.

## Old

In `Sheaf.AlgebraicGeometry.OrbitTensorLineDescent`:

```lean
/-- Pull a section back to an invariant open and transport along the specified equality
of opens. Source: Stacks 0096 (blueprint: lem-per-orbit-tensor-line-descent). -/
noncomputable def orbitInvariantPullback {X : Scheme.{u}} (b : X ⟶ X)
    (F : X.Modules) (U : X.Opens) (hU : b ⁻¹ᵁ U = U) (s : Γ(F, U)) :
    Γ((tensorPullback b).obj F, U) :=
  ((tensorPullback b).obj F).presheaf.map (eqToHom hU.symm).op
    (tensorPullbackSection b F U s)

/-- The tensor of the translates of one section over an invariant open, for the listed
factors. Source: Stacks 01CA, 01CD; the invariant-frame argument of the node
(blueprint: lem-per-orbit-tensor-line-descent). -/
noncomputable def orbitTensorFrameList {H : Type v} {X : Scheme.{u}}
    (a : H → (X ≅ X)) (L : X.Modules) (U : X.Opens)
    (hU : ∀ h : H, (a h).hom ⁻¹ᵁ U = U) (s : Γ(L, U)) :
    (hs : List H) → Γ(pencilTranslateTensor a L hs, U)
  | [] => unitSectionsEquiv U 1
  | h :: hs => tmulSection (orbitInvariantPullback (a h).hom L U (hU h) s)
      (orbitTensorFrameList a L U hU s hs)

/-- An orbit frame is the tensor of all translates of the same section; if that section
is a frame, so is this one. Source: Stacks 01CD, 0BCY; Rydh Proposition 4.7
(blueprint: lem-per-orbit-tensor-line-descent). -/
noncomputable def orbitTensorFrame {H : Type v} [Finite H] {X : Scheme.{u}}
    (a : H → (X ≅ X)) (L : X.Modules) (U : X.Opens)
    (hU : ∀ h : H, (a h).hom ⁻¹ᵁ U = U) (s : Γ(L, U)) :
    Γ(pencilOrbitBundle a L, U) :=
  orbitTensorFrameList a L U hU s (pencilGroupElements H)

/-- Pure tensor sections in the existing tensor power, including the section 1 in degree
zero. Source: Stacks 01CA (blueprint: lem-per-orbit-tensor-line-descent). -/
noncomputable def orbitPowerSection {X : Scheme.{u}} (F : X.Modules) (U : X.Opens) :
    (d : ℕ) → (Fin d → Γ(F, U)) → Γ(F.tensorPow d, U)
  | 0, _ => unitSectionsEquiv U 1
  | d + 1, s => tmulSection (s 0) (orbitPowerSection F U d (fun i ↦ s i.succ))

/-- The canonical linearization on a module pulled back from the quotient. It is the
normalized composition comparison followed by q a = q, with no choice of scalar.
Source: Stacks 0097 (blueprint: lem-per-orbit-tensor-line-descent). -/
noncomputable def orbitQuotientPullbackIso {X Y : Scheme.{u}} (q : X ⟶ Y)
    (b : X ⟶ X) (hb : b ≫ q = q) (M : Y.Modules) :
    (tensorPullback b).obj ((tensorPullback q).obj M) ≅ (tensorPullback q).obj M :=
  ((tensorPullbackSectionComp b q).app M).symm ≪≫
    eqToIso (congrArg (fun f : X ⟶ Y ↦ (tensorPullback f).obj M) hb)

/-- The identity comparison used in the orbit linearization law.
Source: Stacks 0097 (blueprint: lem-per-orbit-tensor-line-descent). -/
noncomputable def orbitLinearizationUnit {H : Type v} [One H] {X : Scheme.{u}}
    (a : H → (X ≅ X)) (a_one : (a 1).hom = 𝟙 X) (F : X.Modules) :
    (tensorPullback (a 1).hom).obj F ≅ F :=
  eqToIso (congrArg (fun b : X ⟶ X ↦ (tensorPullback b).obj F) a_one) ≪≫
    (tensorPullbackSectionId X).app F

/-- The composition comparison used in the orbit linearization cocycle. The order is
contravariant: a_(gh) = a_g composed with a_h.
Source: Stacks 0097 (blueprint: lem-per-orbit-tensor-line-descent). -/
noncomputable def orbitLinearizationComp {H : Type v} [Mul H] {X : Scheme.{u}}
    (a : H → (X ≅ X))
    (a_mul : ∀ g h : H, (a (g * h)).hom = (a h).hom ≫ (a g).hom)
    (F : X.Modules) (g h : H) :
    (tensorPullback (a (g * h)).hom).obj F ≅
      (tensorPullback (a h).hom).obj ((tensorPullback (a g).hom).obj F) :=
  eqToIso (congrArg (fun b : X ⟶ X ↦ (tensorPullback b).obj F) (a_mul g h)) ≪≫
    (tensorPullbackSectionComp (a h).hom (a g).hom).app F

```

The item publicly imported TensorPullbackSectionAdjunction, AmpleCurveTwoSectionPencil,
TensorSection, RingedSiteModules, CochainTensorUniverses and Mathlib's Finite morphisms.
It privately imported FiniteTrivializeInvertibleUpstairs and InvertiblePullbackTensor.

## New

The seven definitions above are verbatim in
`Sheaf.AlgebraicGeometry.OrbitTensorLineSections`, except their blueprint tags now
refer to their own definition node. The item has:

```lean
public import Sheaf.AlgebraicGeometry.OrbitTensorLineSections
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.OrbitTensorLocalFrames
import Sheaf.AlgebraicGeometry.OrbitTensorPermutationLinearizations
import Sheaf.AlgebraicGeometry.InvariantFrameLineDescent
```

The first three former public imports remain publicly available through the new base.
CochainTensorUniverses also remains public through AmpleCurveTwoSectionPencil.
RingedSiteModules is an unused general-site abbreviation; it is removed from this
module's public imports. Scheme module sheaves and all instances required by the
unchanged signature are already provided by the scheme-module imports.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OrbitTensorLineDescent | A4 | Same statement, public names and real-data bodies; proof assembled from the three proper steps. |

A search of all `lean/` found no direct importers of the item and no other Lean uses
of the seven extracted names. The unfinished projective-finite-group-quotient parent
still cites the original node in its argument; its dependency is preserved.
There are no existing consumers to adapt or compile. Every new module and the item
were individually compiled through lcompile.py.

## Status

landed 20261026T091041-L-3301973 2026-10-26 (merge of deliver/A4/Sheaf.AlgebraicGeometry.OrbitTensorLineDescent)
