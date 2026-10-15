/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Connected.Clopen
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.Coherent
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.Mathlib.RingTheory.Artinian.Ring

/-!
# Global functions on a proper reduced scheme over an algebraically closed field

Source: Stacks Project, Varieties, Tag 0BUG, clauses (1)--(3)
(blueprint: lem-weil-pbc-proper-reduced-algclosed-global-sections-product).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Global functions are the product of the scalars indexed by connected components.
Source: Stacks Project, Varieties, Tag 0BUG, clauses (1)--(3)
(blueprint: lem-weil-pbc-proper-reduced-algclosed-global-sections-product).
The ring equivalence commutes with the actual scalar structure map, making it a
`k`-algebra equivalence. Its germ formula specifies the canonical constant-on-components map.

Proof plan:
1. Properness gives finite type over the Noetherian scheme `Spec k`, so `X` is Noetherian
   (`lem-weil-pbc-finite-type-over-noetherian`, `pqf-def-locnoeth`).
2. The structure sheaf is quasi-coherent of finite type, hence coherent by
   `pqf-lem-coherent-ft-locnoeth`. The affine-base degree-zero clause of `lem-pc-coherent-hi`
   makes its global sections finite-dimensional over `k`.
3. Indicator sections of a finite nonempty clopen partition are linearly independent:
   evaluate their germs at a point of each part. Thus partition sizes are bounded by the
   dimension. A partition of maximal size has connected parts, since otherwise it refines.
4. Those parts are precisely the maximal nonempty connected subsets: a connected subset
   cannot meet both a clopen part and its complement. This proves finiteness and clopenness.
5. Sections on a part extend by zero, so their algebra is finite-dimensional and reduced.
   It is nonzero, and `lem-pc-scheme-connected-iff-idempotents` gives trivial idempotents.
   `lem-pc-alg-closed-reduced-algebra-no-idempotents-dim-one` makes its scalar map bijective.
6. Sheaf uniqueness and gluing identify global sections with the product of these algebras.
   Invert restriction and compose with their scalar maps to obtain the specified equivalence.
   For the empty scheme there are no components and the empty-cover sheaf axiom gives the
   zero ring of sections; the empty product is also the zero ring. -/
theorem proper_reduced_globalSections_product
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    [IsProper (X ↘ Spec (CommRingCat.of k))] [IsReduced X] :
    Finite (ConnectedComponents X) ∧
      (∀ x : X, IsClopen (connectedComponent x)) ∧
      (∃ e : (ConnectedComponents X → k) ≃+* Γ(X, ⊤),
        (∀ a : k, e (fun _ ↦ a) =
          (X ↘ Spec (CommRingCat.of k)).appTop
            ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a)) ∧
        ∀ (a : ConnectedComponents X → k) (x : X),
          X.presheaf.germ ⊤ x trivial (e a) =
            X.presheaf.germ ⊤ x trivial
              ((X ↘ Spec (CommRingCat.of k)).appTop
                ((Scheme.ΓSpecIso (CommRingCat.of k)).inv (a (ConnectedComponents.mk x))))) ∧
      (IsEmpty X → IsEmpty (ConnectedComponents X) ∧
        Subsingleton (ConnectedComponents X → k) ∧ Subsingleton Γ(X, ⊤)) := by
  sorry

end AlgebraicGeometry.Scheme
