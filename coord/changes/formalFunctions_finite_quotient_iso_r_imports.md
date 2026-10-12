# AlgebraicGeometry.formalFunctions_finite_quotient_iso_r

## Reason

Prune the public import of FormalFunctionsFiniteQuotientIsoB, whose theorem is
unused by this conditional linear-map construction. Retain all three of B's public
statement dependencies directly. The existing theorem signature and visibility are
identical. No definition or mathematical statement changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientIsoB
```

## New

```lean
public import Sheaf.AlgebraicGeometry.FormalFunctionsFinitePullback
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
```

## Users

The downstream search with `--uses AlgebraicGeometry.formalFunctions_finite_quotient_iso_r`
finds exactly the following two source modules using the declaration. A direct-import
search finds only FormalFunctionsFiniteQuotientIso importing the changed module.
It imports R privately and B independently, so no downstream public interface loses
B's theorem. No source adaptations are needed, and no target meaning changes.
The only other use of B's theorem in the whole library is that same parent module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientIsoR | C1 | Own theorem proved; signature unchanged. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientIso | unclaimed | Calls unchanged R theorem, and already imports B independently; no change needed. |

### Returned review F: unchanged direct-importer source and compile

The source below is the complete, unchanged delivery-base file
`lean/Sheaf/AlgebraicGeometry/FormalFunctionsFiniteQuotientIso.lean`.
It was recovered read-only from the local object database, not reconstructed
from the theorem or replaced by the reviewer's stale, sorry-only version.

- Returned delivery: `f065cdcf09d9affa88f2ba981dcef95fe01d69fb`.
- Its parent (delivery base): `0598a8317d043664afba0354238cbda1cc9b02fc`.
- Importer blob at both base and returned delivery: `30ca1dedc8e7e09b3d260e580f1ba78f0b5ab3ad`.
- Source SHA-256: `c621d5bac48062096c442e11ae716180f6e1c2935ebb6a44c5d98b0d9c617d28`.

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module
public import Sheaf.AlgebraicGeometry.FormalFunctionsFinitePullback
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientIsoB
import Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientIsoR
@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
namespace AlgebraicGeometry
/-- The canonical quotient-system isomorphism, with its factorization of pullback.
Source: Stacks Project, Tags 02OD and 089W; Tags 01F7 and 01FB.
(blueprint: lem-weil-pbc-formal-functions-finite-quotient-iso)

Proof: Write A = O_y, g' : X' → X and i'_n = formalFunctionsFiniteι f y n.
Pasting the pullback squares shows that i'_n is the base change of
Spec(A/m^(n+1)) → Spec A, with ideal J^(n+1). Pullback of F' along i'_n
identifies with F_n: the identification is fixed by the equation of adjunction
units in formalFunctionsFiniteFMap. Coherence implies quasi-coherence, preserved
by tensor pullback. The closed-immersion unit quotient theorem therefore gives
rho_n : F'/J^(n+1)F' ≅ i'_(n*)F_n, with rho_n q_n equal to this h-map.
Apply H^p to rho_n and compose with the affine cohomology edge isomorphism 089W
to obtain b_n. The edge map is the canonical cohomology h-map. Functoriality
then identifies b_n H^p(q_n) with formalFunctionsFinitePullback f y F p n.
Linearity of h-map cohomology and the scalar identity obtained by applying
Gamma-Spec naturality to i'_n show that this pullback is A-linear; let r_n
be this same additive map with that linear structure. Evaluation of algebraMap A
in the completion at level n+1 is Ideal.Quotient.mk, so b_n is also linear
for precisely the restricted completed action displayed here. For adjacent
levels compare the two maps from F'/J^(n+2)F' into i'_(n*)F_n after the epi q_(n+1).
Their composites both equal the unit for i'_n by pullback composition and the
adjunction-unit equation defining formalFibreTransitionFMap. Cancel that epi,
then apply cohomology functoriality to get naturality of b_n. Every arrow of
N opposite is a composite of adjacent arrows; the component isomorphisms
assemble into b. The quotient-unit equation gives the first displayed equality,
and the definition of r_n gives the second. This uses no stalk comparison or
Theta compatibility, and works for degree zero, zero F and an empty fibre. -/
theorem formalFunctions_finite_quotient_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [IsLocallyNoetherian Y] (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) (y : Y) (p : ℕ) :
    let X' := pullback (Y.fromSpecStalk y) f
    let f' := pullback.fst (Y.fromSpecStalk y) f
    let F' := (Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F
    let J := (Scheme.IdealSheafData.ofIdealTop
      ((maximalIdeal (Y.presheaf.stalk y)).map
        (Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv.hom)).comap f'
    let C := RingedSpace.moduleCohomology X'.toRingedSpace p ⋙
      ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫ f'.appTop).hom
    ∃ b : formalCompletionSystem J F' ⋙ C ≅
      formalFibreCohomologySystem f y F p ⋙ ModuleCat.restrictScalars
        (algebraMap (Y.presheaf.stalk y)
          (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))),
    ∃ r : ∀ n : ℕ, formalFunctionsLocalCohomology f y F p →ₗ[Y.presheaf.stalk y]
      formalFibreCohomologyLocal f y F p n,
      (∀ (n : ℕ) (z : formalFunctionsLocalCohomology f y F p),
        r n z = (b.hom.app (op n)) ((C.map (formalModuleQuotientπ J (n + 1) F')) z)) ∧
      ∀ (n : ℕ) (z : formalFunctionsLocalCohomology f y F p),
        r n z = formalFunctionsFinitePullback f y F p n z := by
  dsimp
  obtain ⟨b, hb⟩ := formalFunctions_finite_quotient_iso_b f F hF y p
  obtain ⟨r, hr, hp⟩ := formalFunctions_finite_quotient_iso_r f F hF y p b hb
  exact ⟨b, r, hr, hp⟩
end AlgebraicGeometry
```

To repeat the required check, put this exact source and the delivered R source
beside each other under a fresh scratch sandbox's `lean/Sheaf/AlgebraicGeometry/`
directory, keeping their original filenames. Run
`python3 /home/ubuntu/weil-launcher/lcompile.py --all <scratch sandbox>`.
This compiles R first into that scratch sandbox's `.lbuild`; the importer's
`--setup` then resolves R to that newly compiled delivered object, not the
shared green-build version. B is independently imported by the unchanged importer
and resolves from the shared compiled library. Do not add the importer to the
delivery's `lean/` tree: it is review evidence, not an adaptation.

Executed in this item's `scratchpad/importer-review` on 2026-10-13:

```text
== Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientIsoR (compiled)
[7.2 s]
== Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientIso (compiled)
[12.5 s]
[exit code 0: compiled]
```

Both files compiled without errors or warnings. The R source in this check is
byte-for-byte identical to the delivered module. The unchanged importer really
calls both `formalFunctions_finite_quotient_iso_b` and
`formalFunctions_finite_quotient_iso_r`; thus the check exercises the public-import
change. No proof, signature, node, or importer adaptation is requested or added.

## Status

landed 20261012T223359-L-1634530 2026-10-12 (merge of deliver/C1/Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientIsoR)
