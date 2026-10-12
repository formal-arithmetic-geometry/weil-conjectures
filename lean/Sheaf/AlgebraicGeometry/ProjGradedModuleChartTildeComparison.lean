/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.Algebra.Module.DegreeZeroFractions
public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.Algebra.Module.GradedModuleAwayRestriction
import Sheaf.Topology.SheafOfModulesFromBasis

/-!
# Tilde comparison on a single graded-module chart

Source: Stacks Project, Constructions, Section 01M3 and Lemmas 01M4, 01M7 and 01MB.
(blueprint: lem-weil-pbc-proj-graded-module-chart-tilde-comparison)
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace
open LocalizedModule HomogeneousLocalization

namespace AlgebraicGeometry.Proj

variable {S M : Type u} [CommRing S] [AddCommGroup M] [Module S M]
variable (𝒜 : ℕ → AddSubgroup S) [GradedRing 𝒜]

/-- Restrict the ordinary localized module action along the inclusion of the homogeneous
localization. This changes only scalars, not the localization or its operations.
Source: Stacks, Algebra, Section 00JM.
(blueprint: lem-weil-pbc-proj-graded-module-chart-tilde-comparison) -/
local instance localizedModuleHomogeneousScalarsChartComparison (T : Submonoid S) :
    Module (HomogeneousLocalization 𝒜 T) (LocalizedModule T M) :=
  Module.compHom (LocalizedModule T M)
    (algebraMap (HomogeneousLocalization 𝒜 T) (Localization T))

set_option quotPrecheck false

local notation "Fidx" => {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}
local notation "R[" f "]" => HomogeneousLocalization.Away 𝒜 (f).val.1
local notation "N[" f "]" => LocalizedModule.Away (f).val.1 M
local notation "D[" f "]" => basicOpen 𝒜 (f).val.1
local notation "ModX" => SheafOfModules (moduleRings (Proj 𝒜).toRingedSpace)

/-- On each positive homogeneous chart the given sheaf is the tilde of its degree-zero
module, transported along the canonical affine chart isomorphism.
Source: Stacks Project, Constructions, Section 01M3, Lemmas 01M4, 01M7 (2), and 01MB;
Schemes, Lemma 01HV and Section 01I6.
(blueprint: lem-weil-pbc-proj-graded-module-chart-tilde-comparison)

Proof:
Fix a chart f of degree d > 0. For r in S_(f), choose a homogeneous presentation
r = a/f^n, with a of degree n*d, and set h = f*a. Its degree (n+1)*d is positive,
including when a = 0. Under basicOpenIsoSpec, D_+(h) inside D_+(f) is D(r): the
principal localization element h^d/f^((n+1)*d) is r^d. Localization at r^d is the
same as localization at r since d > 0. Conversely these opens cover the principal
basis of Spec S_(f).

Use gradedModuleAwayRestriction for the degree-zero fraction submodules. Its
comparison theta identifies the module on D_+(h) with the localization of Z f
at r^d, and hence at r. Its submodules equal the specified Z by hZ. To compare
its restriction maps to the specified rho, choose a homogeneous relation h^e=b*f
from hlaws. Every element of the ordinary localization is y/f^m; the two maps
have the same image b^m*y/h^(e*m) by their fraction formulas. Equality follows
by injectivity of the inclusions of Z into the ordinary localized modules.
The ring maps agree as well: hcanonical and uniqueness of ring maps out of S_f
identify their ambient maps, and the inclusion of S_(h) into S_h is injective.
Thus the comparisons are linear for the canonical structure-sheaf restrictions.

Compose these comparisons with alpha, using hscalar and hrestriction. The result
identifies sections of the restriction of F on each principal open with those
of tilde (Z f), whose principal-open sections are localized modules by tilde.toOpen.
For nested principal opens, both restrictions agree on Z f and hence agree by
the localization universal property; this also follows from the comparison
composition law in gradedModuleAwayRestriction. These linear equivalences form
an isomorphism on the principal-open basis. Extend it and its inverse to sheaves
using basis-extension uniqueness; their composites are identities because that
holds on the basis. Transport through basicOpenIsoSpec to obtain the stated iso.
For a nilpotent denominator both localizations are zero; for r=0 the principal
open is empty and the same localization comparison holds. No nonemptiness of a
chart, no finite generation, and no degree-one generation of S is used. -/
theorem gradedModuleChart_tildeComparison
    (𝓜 : ℤ → AddSubgroup M) (h𝓜 : DirectSum.IsInternal 𝓜)
    (hsmul : ∀ (n : ℕ) (z : ℤ) (a : S) (y : M),
      a ∈ 𝒜 n → y ∈ 𝓜 z → a • y ∈ 𝓜 (n + z))
    (Z : ∀ f : Fidx, Submodule R[f] N[f])
    (hZ : (∀ f : Fidx, (Z f : Set N[f]) = degreeZeroFractions
        (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 n : Set M))
        (Submonoid.powers f.val.1)))
    (rhoS : ∀ (f g : Fidx), D[g] ≤ D[f] → R[f] →+* R[g])
    (rho : ∀ (f g : Fidx), D[g] ≤ D[f] → Z f →+ Z g)
    (hlaws : (∀ (f g : Fidx) (i : D[g] ≤ D[f]),
        (∃ (e k : ℕ) (a : S), 0 < e ∧ a ∈ 𝒜 k ∧ g.val.1 ^ e = a * f.val.1) ∧
        (∀ (r : R[f]) (q : Z f), rho f g i (r • q) = rhoS f g i r • rho f g i q) ∧
        (∀ (e k : ℕ) (a : S), 0 < e → a ∈ 𝒜 k → g.val.1 ^ e = a * f.val.1 →
          ∀ (m : ℕ) (y : M) (q : Z f),
            (q : N[f]) = mk y (⟨f.val.1 ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f.val.1) →
            (rho f g i q : N[g]) = mk (a ^ m • y)
              (⟨g.val.1 ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g.val.1))) ∧
      (∀ (f : Fidx) (i : D[f] ≤ D[f]) (q : Z f), rho f f i q = q) ∧
      (∀ (f g h : Fidx) (i : D[g] ≤ D[f]) (j : D[h] ≤ D[g]) (q : Z f),
        rho g h j (rho f g i q) = rho f h (j.trans i) q) ∧
      (∀ (f g : Fidx) (i : D[g] ≤ D[f]), D[f] = D[g] →
        Function.Bijective (rho f g i)))
    (hcanonical : ∀ (f g : Fidx) (i : D[g] ≤ D[f]),
      ∃ l : Localization.Away f.val.1 →+* Localization.Away g.val.1,
        (∀ a : S, l (algebraMap S (Localization.Away f.val.1) a) =
          algebraMap S (Localization.Away g.val.1) a) ∧
        ∀ r : R[f], (rhoS f g i r).val = l r.val)
    (F : ModX) (alpha : ∀ f : Fidx, F.val.obj (op D[f]) ≃+ Z f)
    (hscalar : ∀ (f : Fidx) (r : R[f]) (s : F.val.obj (op D[f])),
      alpha f ((awayToSection 𝒜 f.val.1 r) • s) = r • alpha f s)
    (hrestriction : ∀ (f g : Fidx) (i : D[g] ≤ D[f])
      (s : F.val.obj (op D[f])),
      alpha g (F.val.map (homOfLE i).op s) = rho f g i (alpha f s)) :
    ∀ f : Fidx, Nonempty
      (Scheme.Modules.restrict F D[f].ι ≅
        Scheme.Modules.restrict (tilde (ModuleCat.of R[f] (Z f)))
          (basicOpenIsoSpec 𝒜 f.val.1 f.property.2 f.property.1).hom) := by sorry


end AlgebraicGeometry.Proj
