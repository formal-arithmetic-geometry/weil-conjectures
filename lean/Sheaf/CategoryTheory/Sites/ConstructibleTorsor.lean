module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.CategoryTheory.Sites.Torsor

/-!
# Torsors on the small étale site

Source: Stacks Project, Cohomology on Sites, Definition 03AH, label
`definition-torsor` (blueprint: def-constructible-torsor).
-/

@[expose] public section

universe u v w

open CategoryTheory Opposite

namespace CategoryTheory.Sheaf

/-- A torsor under a possibly non-commutative sheaf of groups on the small étale site.

The action is given on sections and is compatible with restriction.  Simple transitivity is
expressed by bijectivity after fixing any section, and local non-emptiness is expressed by the
covering sieve of objects carrying a section.  Source: Stacks Project, Cohomology on Sites,
Definition 03AH, label `definition-torsor` (blueprint: def-constructible-torsor). -/
structure NonabelianTorsor (X : AlgebraicGeometry.Scheme.{u})
    (G : Sheaf X.smallEtaleTopology GrpCat.{v}) where
  /-- The underlying sheaf of sets. -/
  sheaf : Sheaf X.smallEtaleTopology (Type w)
  /-- The left action of the group sheaf on the underlying sheaf. -/
  act (U : X.Etaleᵒᵖ) : G.obj.obj U → sheaf.obj.obj U → sheaf.obj.obj U
  one_act (U : X.Etaleᵒᵖ) (t : sheaf.obj.obj U) : act U 1 t = t
  mul_act (U : X.Etaleᵒᵖ) (g h : G.obj.obj U) (t : sheaf.obj.obj U) :
    act U (g * h) t = act U g (act U h t)
  map_act {U V : X.Etaleᵒᵖ} (f : U ⟶ V) (g : G.obj.obj U) (t : sheaf.obj.obj U) :
    sheaf.obj.map f (act U g t) = act V ((G.obj.map f).hom g) (sheaf.obj.map f t)
  /-- The action is simply transitive on sections whenever they are nonempty. -/
  bijective_act (U : X.Etaleᵒᵖ) (t : sheaf.obj.obj U) :
    Function.Bijective (act U · t)
  /-- Every object is covered by objects over which the torsor has a section. -/
  nonemptySieve_mem (U : X.Etale) :
    nonemptySieve sheaf.obj U ∈ X.smallEtaleTopology U

namespace NonabelianTorsor

variable {X : AlgebraicGeometry.Scheme.{u}}
variable {G : Sheaf X.smallEtaleTopology GrpCat.{v}}

/-- A sheaf isomorphism from a torsor to the translation torsor over an object `U`.

The family is indexed by objects `V → U` of the slice of the small étale site; `natural`
expresses compatibility with restriction and `equivariant` expresses compatibility with left
translation.  Source: Stacks Project, Cohomology on Sites, Definition 03AH, label
`definition-torsor` (blueprint: def-constructible-torsor). -/
structure Trivialization (P : NonabelianTorsor X G) (U : X.Etale) where
  equiv : ∀ (V : X.Etale) (_f : V ⟶ U),
    P.sheaf.obj.obj (op V) ≃ G.obj.obj (op V)
  natural : ∀ {V W : X.Etale} (f : V ⟶ U) (g : W ⟶ V)
      (t : P.sheaf.obj.obj (op V)),
    equiv W (g ≫ f) (P.sheaf.obj.map g.op t) =
      (G.obj.map g.op).hom (equiv V f t)
  equivariant : ∀ (V : X.Etale) (f : V ⟶ U)
      (a : G.obj.obj (op V)) (t : P.sheaf.obj.obj (op V)),
    equiv V f (P.act (op V) a t) = a * equiv V f t

/-- Triviality of a torsor over `U`: it is isomorphic there to the group sheaf with left
translation.  Source: Stacks Project, Cohomology on Sites, Definition 03AH, label
`definition-torsor` (blueprint: def-constructible-torsor). -/
def IsTrivialOver (P : NonabelianTorsor X G) (U : X.Etale) : Prop :=
  Nonempty (Trivialization P U)

end NonabelianTorsor

end CategoryTheory.Sheaf
