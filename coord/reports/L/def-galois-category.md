# def-galois-category (L, stage 2)

## Worker report

Worker W-gal0508 (group L). Module `Sheaf.CategoryTheory.Galois.StacksGaloisCategory`
(`lean/Sheaf/CategoryTheory/Galois/StacksGaloisCategory.lean`, written in `lean/.sandbox/L/`) defines
`structure CategoryTheory.IsStacksGaloisCategory {C : Type u} [Category.{v} C] (F : C ⥤ Type w) : Prop`,
Stacks Tag 0BMY: the pair `(C, F)` is a Galois category. Compiles clean (no error, no warning).

Choice: a new definition (not `existing`). Mathlib's `GaloisCategory` + `PreGaloisCategory.FiberFunctor`
(SGA1/Lenstra G1–G6) is not the node's notion clause by clause: Mathlib assumes only terminal, pullbacks,
finite coproducts and quotients by finite groups (not coequalizers/all finite colimits), a fibre functor
preserving those and epis (not all finite colimits), assumes G3 (not in 0BMY), and derives 0BMY(2)
(`has_decomp_connected_components`); no Mathlib theorem proves the equivalence in both directions.

Clause -> Lean:
- `C` a category, `F : C → Sets`: `{C : Type u} [Category.{v} C] (F : C ⥤ Type w)` (all universes free).
- (1) finite limits and finite colimits: fields `hasFiniteLimits : HasFiniteLimits C`,
  `hasFiniteColimits : HasFiniteColimits C` (node def-galois-finite-limits-colimits).
- (2) every object a finite (possibly empty) coproduct of connected objects: field
  `exists_finite_coproduct_isConnected (X : C) : ∃ (ι : Type) (_ : Finite ι) (f : ι → C)
  (g : (i : ι) → f i ⟶ X), Nonempty (IsColimit (Cofan.mk X g)) ∧ ∀ i, IsConnected (f i)`
  (def-galois-finite-coproduct: Cofan/IsColimit, pattern of Decomposition.lean 120; empty ι allowed;
  def-galois-connected-object: `PreGaloisCategory.IsConnected`, checked: `notInitial : IsInitial X → False`
  and `noTrivialComponent : ∀ Y (i : Y ⟶ X) [Mono i], (IsInitial Y → False) → IsIso i`, which is
  "every mono is an iso or has initial source" classically; def-galois-initial-mono: IsInitial, Mono).
- (3) `F(X)` finite: field `finite_obj (X : C) : Finite (F.obj X)`.
- (4) exact: fields `preservesFiniteLimits : PreservesFiniteLimits F`,
  `preservesFiniteColimits : PreservesFiniteColimits F` (def-galois-exact-functor); reflects isos:
  `reflectsIsomorphisms : F.ReflectsIsomorphisms` (def-galois-reflects-isomorphisms).
- Last paragraph (Aut(F) ⊂ ∏ Aut(F(X)) with the induced topology, def-galois-aut-topology): a construction,
  not a condition; stated in the docstring as realized by Mathlib's
  `PreGaloisCategory.instTopologicalSpaceAutFunctorFintypeCat` (induced by `PreGaloisCategory.autEmbedding`)
  for `F` regarded as a functor to `FintypeCat`. No Lean field.

Dependency declarations: all Mathlib (import `Mathlib.CategoryTheory.Galois.Basic` only).

Edge cases: empty index type in (2) allowed (initial objects are the empty coproduct); `ι : Type` covers
every finite cardinality; `Type w` for Sets with `w` free; `C` with any universes.

Searches: the node's `mathlib_searches` (leansearch, leanfinder, grep, local_search; no Stacks-style Galois
category in Mathlib or WeilConjectures/); grep of `StacksGalois` in Mathlib, WeilConjectures/,
`dag/lean_names_upstream.json`, `lean/Sheaf`: no hit, so the name is free.

Doubt: (2) uses `Nonempty (IsColimit …)` inside an `∃` (Prop), where Mathlib's theorem uses the data
`IsColimit` as an `∃` binder; equivalent. No STATEMENT-DISPUTED, no node fault.

## Second reading by L

Independent review by R-gal0511 (reviewer sub-agent of L): PASS; every clause matched; see reviewed_lean on the node.
