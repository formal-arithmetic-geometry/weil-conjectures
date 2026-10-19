/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.KrullDimension
public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
import Sheaf.AlgebraicGeometry.NormalModificationCodimensionOne
import Sheaf.AlgebraicGeometry.ClosedPointField
import WeilConjectures.AlgebraicGeometry.ProperBasic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Sheaf.AlgebraicGeometry.NormalSurfaceExceptionalCurves

/-!
# Exceptional curves of a normalized dominating graph

Source: Stacks Project, Resolution of Surfaces, Tag 0BBT, third proof paragraph,
with the reduced dominating component in place of the entire fibre product
(blueprint: lem-per-normalized-surface-graph-exceptional-injection).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- The normalized dominating graph of two proper birational normal excellent surfaces
injects the exceptional curves of its second projection into those of the original map.

The point `t` lies over the generic point of `X`; its closure with the reduced induced
structure is specified by the reduced closed immersion `i` and `hW`. Integrality of `W`
is asserted before it is used. After installing that proved property, `e` and `hν` merely
name a representative of its canonical normalization, and `hp` and `hf'` name the actual
projections. Integrality of `Z` is likewise asserted before its function field is used.
The equations `hB` and `hB'` specify the exceptional curves by their underlying closed
irreducible subsets; these carry the unique reduced induced scheme structures.
The local-ring equality is equality of their canonical images in `k(Z)`, identified with
`K = k(X)` by the asserted function-field isomorphisms.

Source: Stacks Project, Resolution of Surfaces, Tag 0BBT, third proof paragraph
(blueprint: lem-per-normalized-surface-graph-exceptional-injection).

Proof (the eight steps of the DAG):
1. Apply lem-per-normal-modification-codimension-one to f and g. Their isomorphism opens
   contain the generic point; intersect them to get U. The fibre product over U is U.
   The closure of its generic point is irreducible and its reduced structure W is integral,
   with the same generic local field (def-pc-fibre-product, def-sc-function-field).
2. The projections of the fibre product are proper by lem-weil-pbc-proper-base-change;
   restrict to W using lem-weil-pbc-closed-immersion-proper and compose using
   lem-weil-pbc-proper-composition. Apply lem-per-normal-surface-exceptional-curves to
   W -> X: normalization is finite, normal, integral, excellent, Noetherian and of
   dimension two. Its projections are proper and induce the specified field isomorphisms.
3. For an exceptional curve C', lem-per-normal-surface-exceptional-curves makes its
   contraction point x' closed and gives transcendence degree one at its generic point.
   Properness makes x = g(x') closed (pqf-lem-proper-basic). Apply
   lem-kun-closed-point-field to the finite-type fibre of g to make kappa(x')/kappa(x) finite.
4. If p(C') were a point y, properness makes y closed and the same closed-point lemma
   makes kappa(y)/kappa(x) finite. The residue-field fibre-product model
   (lem-weil-pbc-fibre-product-affine-spectra) is the spectrum of
   kappa(y) tensor kappa(x'). It is finite-dimensional over kappa(x), and its prime
   quotients are fields by lem-weil-pbc-finite-dimensional-domain-is-field.
5. The finite normalization also has finite residue extensions: base change its finite
   affine algebra to a residue field and apply that same finite-dimensional-domain
   criterion to the prime quotient. Double contraction would therefore make the generic
   residue field of C' finite over kappa(x'), contradicting transcendence degree one.
6. The image C = p(C') is closed and irreducible by properness. It is proper in Y and so
   has dimension at most one by def-kun-topological-krull-dimension. A zero-dimensional
   irreducible closed subset of a sober scheme is a singleton (lem-sc-scheme-sober),
   excluded by Step 5. Thus C is an exceptional curve of f.
7. Its generic local ring is a DVR by lem-per-normal-surface-exceptional-curves. Its
   prime chains have length one (def-sc-discrete-valuation-ring and
   def-weil-pbc-krull-dimension-ring). Apply clause (2) of
   lem-per-normal-modification-codimension-one to p to obtain an isomorphism neighbourhood.
8. A closed continuous map takes the generic point of C' to that of C. The open
   isomorphism gives exactly one point over it, hence injectivity on curves by their
   generic closures (def-sc-generic-point, lem-sc-scheme-sober). The actual stalk map
   identifies the local rings; its generic map gives their equality inside the already
   identified function field (def-sc-function-field). Step 3 gives the residue assertions.
-/
theorem normalized_surface_graph_exceptional_injection
    {X Y X' : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral X']
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X']
    (hXnormal : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    (hYnormal : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
      IsIntegrallyClosed (Y.presheaf.stalk y))
    (hX'normal : ∀ x' : X', IsDomain (X'.presheaf.stalk x') ∧
      IsIntegrallyClosed (X'.presheaf.stalk x'))
    (hXexcellent : ∀ U : X.affineOpens, IsExcellent Γ(X, U))
    (hYexcellent : ∀ U : Y.affineOpens, IsExcellent Γ(Y, U))
    (hX'excellent : ∀ U : X'.affineOpens, IsExcellent Γ(X', U))
    (hXdim : topologicalKrullDim X = 2)
    (hYdim : topologicalKrullDim Y = 2)
    (hX'dim : topologicalKrullDim X' = 2)
    (f : Y ⟶ X) (g : X' ⟶ X) [IsProper f] [IsProper g]
    (hfη : f (genericPoint Y) = genericPoint X)
    (hgη : g (genericPoint X') = genericPoint X)
    (hfK : IsIso (f.functionFieldMap hfη)) (hgK : IsIso (g.functionFieldMap hgη))
    (t : (pullback f g : Scheme.{u})) (ht : (pullback.fst f g ≫ f) t = genericPoint X)
    (W : Scheme.{u}) [IsReduced W] (i : W ⟶ pullback f g) [IsClosedImmersion i]
    (hW : Set.range i = closure ({t} : Set (pullback f g : Scheme.{u}))) :
    IsIntegral W ∧ ∀ [IsIntegral W],
      ∀ (Z : Scheme.{u}) (ν : Z ⟶ W) (e : Z ≅ W.normalization),
        e.hom ≫ W.fromNormalization = ν →
        ∀ (p : Z ⟶ Y) (f' : Z ⟶ X'),
          ν ≫ i ≫ pullback.fst f g = p → ν ≫ i ≫ pullback.snd f g = f' →
          IsFinite ν ∧ IsIntegral Z ∧ IsNoetherian Z ∧
          (∀ z : Z, IsDomain (Z.presheaf.stalk z) ∧
            IsIntegrallyClosed (Z.presheaf.stalk z)) ∧
          (∀ U : Z.affineOpens, IsExcellent Γ(Z, U)) ∧
          topologicalKrullDim Z = 2 ∧ IsProper p ∧ IsProper f' ∧
          (∀ [IsIntegral Z],
            ∃ hpη : p (genericPoint Z) = genericPoint Y,
              ∃ hf'η : f' (genericPoint Z) = genericPoint X',
                IsIso (p.functionFieldMap hpη) ∧ IsIso (f'.functionFieldMap hf'η) ∧
                ∀ (B : Set (Set Y)) (B' : Set (Set Z)),
                  B = {C : Set Y | IsClosed C ∧ IsIrreducible C ∧
                    topologicalKrullDim C = 1 ∧ ∃ x : X, f '' C = {x}} →
                  B' = {C' : Set Z | IsClosed C' ∧ IsIrreducible C' ∧
                    topologicalKrullDim C' = 1 ∧ ∃ x' : X', f' '' C' = {x'}} →
                  (∀ C' ∈ B', p '' C' ∈ B) ∧
                  Set.InjOn (fun C' : Set Z ↦ p '' C') B' ∧
                  (∀ C' ∈ B',
                    (∀ η' : Z, IsGenericPoint η' C' →
                      IsGenericPoint (p η') (p '' C') ∧
                      (∃ U : Y.Opens, p η' ∈ U ∧ IsIso (p ∣_ U)) ∧
                      IsIso (p.stalkMap η') ∧
                      Set.range ((p.functionFieldMap hpη).hom.comp
                        (algebraMap (Y.presheaf.stalk (p η')) Y.functionField)) =
                        Set.range (algebraMap (Z.presheaf.stalk η') Z.functionField)) ∧
                    ∃ x' : X', f' '' C' = {x'} ∧ f '' (p '' C') = {g x'} ∧
                      IsClosed ({x'} : Set X') ∧ IsClosed ({g x'} : Set X) ∧
                      (g.residueFieldMap x').hom.Finite)) := by
  sorry

end AlgebraicGeometry
