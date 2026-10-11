## Worker report

The module states `AlgebraicGeometry.intersection_effectiveCartier` in
`lean/Sheaf/AlgebraicGeometry/IntersectionEffectiveCartier.lean`. It introduces a field `k`,
a proper `k`-scheme `X`, a nonempty closed subscheme `Z` with dimension `d`, invertible
modules `L`, and an invertible ideal sheaf `J` defining a nonempty effective Cartier divisor.
The hypotheses `hdimZ`, `hDim`, and `hIso` render respectively the dimension of `Z`, the
alternative dimension/integrality assumption, and `L₁|Z ≅ O_Z(D)`. The conclusion gives properness
of the divisor, existence of its dimension `d-1`, ampleness after restriction, and the equality
of intersection numbers. The existential dimension proof is used because `intersectionNumber`
requires that proof as an explicit argument.

Dependencies used: `Sheaf.AlgebraicGeometry.IntersectionNumber` (`Scheme.Modules.intersectionNumber`),
`WeilConjectures.AlgebraicGeometry.EffectiveCartier` (`IdealSheafData.IsInvertible`,
`IdealSheafData.subschemeι`, `IdealSheafData.toModules`), and
`WeilConjectures.AlgebraicGeometry.Modules.Ample` (`IsAmple`). Mathlib declarations include
`Field`, `IsProper`, `IsClosedImmersion`, `topologicalKrullDim`, and `IsIntegral`.

Edge cases checked: `d ≥ 1` permits `d=1`, where `Fin (d-1)` is empty; `Nonempty Z` and
`Nonempty J.subscheme` exclude empty intersection schemes; no characteristic restriction is added.
The search records in the node (LeanFinder, Loogle, grep, LeanSearch) found no existing Cartier
intersection formula.

## Earlier second reading (a previous round; superseded)

The file and node were read clause by clause. Every field, dimension, invertibility, effective
Cartier, ampleness, properness, and intersection-number clause has a corresponding Lean binder or
conclusion. The only elaboration-driven presentation choice is existential packaging of the
`dim D = d-1` proof required by `intersectionNumber`; it preserves the node's asserted dimension
and equality.

## Second reading by F1

Independent second reader, 2026-10-11. Read the item JSON, its complete proof, all eleven
statement-dependency nodes, the actual declarations described below, and the delivered Lean.
The node itself is unchanged and has no statement_change. There are no new definition nodes
or dependency modules in this delivery.

Source check: the local clone has no literature/stacks-project/varieties.tex, so fetched the
Stacks repository's varieties.tex into the item's scratchpad and read lines 10540-10625,
labels lemma-numerical-intersection-effective-Cartier-divisor (Tag 0BEU) and
lemma-ample-positive (Tag 0BEV). Also checked the corresponding official tag pages:
https://stacks.math.columbia.edu/tag/0BEU and https://stacks.math.columbia.edu/tag/0BEV.
0BEU supplies the intersection identity and Euler-characteristic difference argument;
0BEV supplies the integral positive-dimensional, nonempty Cartier zero-divisor application.
The DAG deliberately states the nonempty/dimension-specialized form used there, together
with properness and restriction of ampleness. No additional throughout hypothesis on
characteristic, smoothness, geometric integrality, or algebraic closure occurs in the source.

Clause-by-clause inventory and verdict:

1. Field k: `(k : Type u) [Field k]`. Exact; arbitrary characteristic and arbitrary universe u.
2. X proper over k: `(X : Scheme.{u}) [X.Over (Spec (.of k))]` and
   `[IsProper (X ↘ Spec (.of k))]`. Exact. Read Mathlib Proper.lean:42:
   separated, universally closed, locally finite type; universal closedness gives the
   quasi-compactness making this finite type as the dependency node requires.
3. Closed subscheme Z of X: `(Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]`.
   Exact. Read Mathlib ClosedImmersion.lean:45 (closed embedding and stalk surjectivity).
   This is the recorded Mathlib match, not a private closed-subscheme predicate.
4. Dimension d >= 1: `(d : ℕ) (hd : 1 ≤ d)` and
   `hdimZ : topologicalKrullDim Z = ((d : ℕ∞) : WithBot ℕ∞)`.
   Exact. Read the recorded dimension node: the dimension is the supremum of strict
   irreducible-closed chains, with the empty-space value bottom. `[Nonempty Z]` is redundant,
   already forced by this dimension (also by the nonempty divisor), and is required by the
   recorded intersectionNumber; it does not exclude a case of the node.
5. d invertible modules on X: `(L : Fin d → X.Modules)` and
   `[∀ j : Fin d, (L j).IsInvertible]`. Exact. Read source Modules/Invertible.lean:57:
   local isomorphism to the structure sheaf, the same locally free rank-one notion as
   def-sc-invertible-module. Fin uses zero-based indices: `L ⟨0, hd⟩` is L_1.
6. Nonempty effective Cartier divisor D on Z: `(J : Z.IdealSheafData)` with
   `hJ : J.IsInvertible` and `[Nonempty J.subscheme]`; D is J.subscheme and its inclusion
   is J.subschemeι. Exact. Read source Mathlib/AlgebraicGeometry/IdealSheaf/Invertible.lean:56:
   this predicate means affine-locally a nonzerodivisor generates J, not merely a locally
   principal ideal. IdealSheafData is the quasi-coherent ideal notion required by the node.
7. L_1 restricted to Z is O_Z(D):
   `hIso : (Scheme.Modules.tensorPullback i).obj (L ⟨0, hd⟩) ≅
   Scheme.Modules.dual J.toModules`. Exact. Read EffectiveCartier.lean:201-209:
   O_Z(D) is the dual of J.toModules. Read landed TensorPullback.lean:33-95:
   tensorPullback is O_Z tensor over i^-1 O_X with i^-1 L, not Mathlib's different pullback.
   An explicit isomorphism witness is equivalent here to the node's isomorphism hypothesis.
8. Parenthetical zero-section application: the node explains a sufficient way to supply
   hIso, rather than introducing another independent hypothesis on D. Read the recorded
   lem-pc-zero-scheme-divisor-iso declaration Hom.nonempty_iso_dual_toModules_tensorObj
   in Modules/ZeroLocus.lean:692: N is isomorphic to the dual zero-locus ideal tensor M.
   Setting M = O_Z yields the asserted section case. The repaired docstring explicitly
   records this use; no stronger regularity/nonzero-section hypothesis is imposed on hIso.
9. Alternative dimension/integrality assumption: hDim is precisely
   `topologicalKrullDim J.subscheme = ... (d - 1) ... ∨ IsIntegral Z`.
   Exact disjunction, not an integrality instance assumed in both branches. Read Mathlib
   Properties.lean:240: integral means nonempty and domain sections on nonempty opens.
10. Conclusion (a), D proper over k: now
    `IsProper (J.subschemeι ≫ i ≫ X ↘ Spec (.of k))`. Exact induced structure morphism.
    Conclusion dim D = d-1: `∃ hdimD : topologicalKrullDim J.subscheme = ...`.
    Exact. Its proof witness is used as the dimension argument to intersectionNumber.
11. Conclusion (b), every ample invertible M on X restricts to an ample module on D:
    `∀ M : X.Modules, M.IsInvertible → IsAmple (X ↘ Spec (.of k)) M →
    IsAmple (J.subschemeι ≫ i ≫ X ↘ Spec (.of k))
    ((Scheme.Modules.tensorPullback (J.subschemeι ≫ i)).obj M)`.
    Exact. Read source Modules/Ample.lean:101 and 174: IsVeryAmple is a closed
    projective-space immersion over the named base and IsAmple is a positive very ample
    power. On proper schemes this is precisely the dependency node's notion.
12. Conclusion (c), intersection equality:
    `intersectionNumber k X Z i d hdimZ L =
    intersectionNumber k X J.subscheme (J.subschemeι ≫ i) (d - 1) hdimD
    (fun j : Fin (d - 1) ↦ L ⟨j.1 + 1, by omega⟩)`.
    Exact: the remaining bundles are L_2,...,L_d on the same ambient X, and the divisor
    immersion is the composite. Read landed IntersectionNumber.lean:40-56: coefficient
    of the all-one monomial in the Euler polynomial for i_*O_Z and the given twists;
    its dimension proof is an explicit argument. Existentially packaging that proof
    changes neither the identity nor the dimension assertion (proof irrelevance).

Edge cases: d=0 is excluded exactly by the node's d>=1, not by an additional restriction.
d=1 is included: Fin (d-1) is empty and intersectionNumber reads the constant coefficient.
Empty D is excluded by the node; empty Z and X cannot have a nonempty closed D, and Z's
positive finite dimension independently excludes its emptiness. The zero O_X-module is
not invertible on these nonempty schemes. A nowhere-vanishing section gives an empty zero
scheme and hence falls outside the stated nonempty-D case. No bound on characteristic,
no Noetherian hypothesis, no finite-type hypothesis beyond properness, no irreducibility
in the dimension-assumed branch. `universe u` is explicit throughout; schemes, field,
modules, and finite index sets are in their natural common ambient universe, with no
quantification over test objects in an independently smaller universe. No binder is unbound.

Independent searches (all run on this reading; searches.jsonl records service results):

- LeanFinder via msearch.py: "Euler characteristic difference Cartier divisor intersection
  product restriction". Returned basic-open/zero-locus facts and unrelated incidence
  algebra Euler characteristics, no Cartier intersection-number formula.
- Loogle via msearch.py: "AlgebraicGeometry.Scheme.Modules.intersectionNumber".
  The service does not know this project declaration; zero matches. Direct source reading
  establishes that the landed declaration is a definition, not the theorem being delivered.
- LeanSearch via msearch.py: "intersection product with divisor associated line bundle
  restriction". Unavailable (Internal Server Error); no mathematical no-match verdict inferred.
- msearch grep "intersection|Cartier" and direct rg with
  `intersectionNumber|intersection.*[Cc]artier|[Cc]artier.*intersection|0BEU` over Mathlib,
  WeilConjectures, and lean/Sheaf. Only the existing IntersectionNumber definition and its
  self-intersection abbreviation match the relevant notion; the source Hopf-algebra Cartier
  lemma is unrelated. No existing full theorem. Searched dag/lean_names_upstream.json
  for both the item id and intersection_effectiveCartier: no declaration-name conflict.

Mismatches repaired:

- H3: Z.Over and J.subscheme.Over were independent, unconstrained structures; the conclusions
  used the latter's arbitrary map to Spec k instead of the composite through X. Removed
  both unnecessary Over binders and stated properness/ampleness for the induced composite.
- H8: the theorem docstring only named four techniques. Replaced it with the complete
  four-step node proof, naming every proof ingredient and the section/zero-divisor application.
- H9: added the project's copyright/license/author header and replaced the unused
  TensorPullbackAdjunction import with TensorPullback, the module whose definition is used.
- Replaced the opaque `by omega` dimension argument with the bound hdimD witness, and
  used the conventional lambda arrow. The finite-index bound proof is the only inline tactic;
  it is a typing condition, not a newly proved mathematical statement.

No hollow data definition was introduced; the only new mathematical theorem is
AlgebraicGeometry.intersection_effectiveCartier and its proof remains sorry. No statement
correction or DAG split was needed. Updated lean.statement to the exact final file signature.
Final server compile via scompile.py of the delivery's actual module: exit code 0, no errors
or warnings. The report's original Worker report and superseded earlier reading are retained.
