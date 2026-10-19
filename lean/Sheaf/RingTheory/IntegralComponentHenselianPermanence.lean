/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Group.Idempotent
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.RingTheory.FilteredColimitHenselianPair
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsSepClosed

/-!
# Connected integral algebras over henselian local rings

Source: Hübner--Schmidt, The tame site of a scheme, printed p. 12, permanence paragraph
citing Artin Proposition 3.3; Stacks Project, More on Algebra, Tags 092X and 09XK
(blueprint: lem-trf-integral-component-henselian-permanence).
-/

@[expose] public section

universe u v

namespace HenselianLocalRing

/-- A nonzero connected integral algebra over a henselian local ring is henselian local;
its structure map is local and its canonical residue-field extension is algebraic.
Strict henselianity of the base implies strict henselianity of the algebra.
Source: Hübner--Schmidt, printed p. 12, permanence paragraph citing Artin Proposition 3.3;
Stacks Project, Tags 092X and 09XK, with the connected specialization of Tag 04GH.
(blueprint: lem-trf-integral-component-henselian-permanence).

Proof:
1. Index S by its finitely generated R-subalgebras. They form a nonempty directed set and
   cover S. Each is module-finite by lem-weil-pbc-finite-of-integral-generators, and inherits
   nonzeroness and the zero-one idempotent condition from its injective inclusion into S.
2. By lem-weil-pbc-finite-over-henselian-local-product, each finite subalgebra is a product
   of henselian local algebras with local structure maps and finite residue extensions.
   Nonzeroness excludes the empty product, and the idempotent condition forces one factor.
3. Every transition is integral. By lem-weil-pbc-integral-maximal-contracts-maximal, its
   maximal ideal contracts to the unique maximal ideal of its source. Thus transitions
   are local and induce injective residue-field maps.
4. The directed union N of these maximal ideals is an ideal not containing 1. An element
   outside N has an inverse in a stage; an element of N cannot become invertible, since
   any purported inverse lies in a common later stage. Hence N is exactly the nonunits,
   S/N is a field, and S is local. The contraction to R is its maximal ideal.
5. The inclusions exhibit S as the ring colimit: compatible maps define a unique map by
   evaluation at a stage containing the element (def-weil-pbc-category-colimit). The stage
   maximal ideals have union N. Apply lem-weil-pbc-filtered-colimit-henselian-pair to these
   pairs; together with locality this gives HenselianLocalRing S, using
   def-weil-pbc-henselian-terminology.
6. Reducing a monic integral equation for a lift of any element of S/N gives a nonzero
   annihilating polynomial over the residue field of R. Thus the canonical residue
   extension is algebraic (def-weil-algebraic-element).
7. If R is strictly henselian, its residue field is separably closed. Each stage residue
   field is separably closed by lem-kun-sep-closed-finite-extension-sep-closed. A separable
   nonconstant polynomial over S/N and Bezout witnesses for it and its derivative have
   finitely many coefficients, all in one stage residue field. Injectivity descends the
   Bezout identity and nonconstancy. A root exists there by def-pc-separably-closed and
   maps to a root in S/N. Thus S/N is separably closed, so S is strictly henselian by
   def-weil-pbc-henselian-terminology. No finiteness, reducedness or domain assumption
   on S is used. -/
theorem integral_component_henselian_permanence
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [HenselianLocalRing R] [Algebra R S] [Nontrivial S] [Algebra.IsIntegral R S]
    (hconnected : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) :
    ∃ (_ : HenselianLocalRing S), ∃ (_ : IsLocalHom (algebraMap R S)),
      @Algebra.IsAlgebraic (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
        _ _ (IsLocalRing.ResidueField.map (algebraMap R S)).toAlgebra ∧
      (IsStrictlyHenselianLocalRing R → IsStrictlyHenselianLocalRing S) := by
  sorry

end HenselianLocalRing
