module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Topology.Sheaves.Flasque

/-! # Flasqueness of the sheaf associated to an injective module

Source: Stacks Project, Tag 09T2, Lemma 36.8.1.
(blueprint: lem-sbc-injective-module-tilde-flasque)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The associated sheaf of an injective module over a Noetherian ring is flasque.
Source: Stacks Project, Tag 09T2, Lemma 36.8.1.
(blueprint: lem-sbc-injective-module-tilde-flasque)

Proof: Spec R is Noetherian. The affine equivalence between R-modules and
quasi-coherent sheaves preserves injectivity, so the sheaf associated to M is
injective in QCoh. Tag 09T2 makes this sheaf flasque. In its proof, a section
on an open extends to a morphism from a power of the coherent ideal defining
the complement. Injectivity extends that morphism along the ideal's inclusion
in the structure sheaf; the resulting global section restricts to the given
section. Thus sections on the whole spectrum surject onto those on every
open. Given V contained in U, extend a section on V globally and restrict
it to U; this proves all restriction maps surjective. Restriction of scalars
to R does not alter these underlying functions, and epimorphisms in ModuleCat
are exactly surjective maps. Therefore the presheaf used by tilde.toOpen is
flasque. The empty open has the zero section module and is included. -/
theorem injective_tilde_isFlasque
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Injective M] :
    TopCat.Presheaf.IsFlasque (modulesSpecToSheaf.obj (tilde (R := .of R) M)).presheaf := by sorry

end AlgebraicGeometry.Scheme
