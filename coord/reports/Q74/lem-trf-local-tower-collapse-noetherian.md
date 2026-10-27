## Worker report

Delivered `Sheaf.RingTheory.LocalTowerCollapseNoetherian`, declaring
`Module.local_tower_collapse_noetherian` with its sole theorem proof `sorry`.
The source is Stacks Algebra, Tag 00R7 (`lemma-criterion-flatness-fibre`),
its approximation paragraphs and the sentence composing tensor localizations;
Tag 07DS (`lemma-composition-essentially-of-finite-type`);
Tag 00FN (`lemma-Noetherian-permanence`); and
Tag 00FP (`lemma-Noetherian-finite-type-is-finite-presentation`), clause (3).
I read these places in `literature/stacks-project/algebra.tex`, including the
successive supplied diagrams and the composite comparison sentence.
The six proof steps of the DAG are carried into the theorem docstring.
The node is unchanged outside `lean`. No new nodes, dependency repairs,
statement corrections, or disputed statements.

`RingHom.IsTensorLocalizationSquare` is a helper in the owning node's module,
listed in `lean.declarations` and bearing the source and blueprint docstring.
It spells out a repeated canonical-map assertion belonging to this item,
using the existing Mathlib tensor product and `Submonoid.IsLocalizationMap`.
Its definition contains real terms and no postponed proof or data. It introduces
no replacement tensor product or localization notion. The existential comparison
ring map is fixed uniquely by the formula on every pure tensor, so the predicate
does not permit an arbitrary unrelated comparison map. Its two `letI` bindings
are inside the helper definition, installing the exact supplied ring maps as
algebra structures; there are no `let`, `have`, or `show` binders in the theorem
signature. Its four ring universes are explicitly declared.

Hypothesis-by-hypothesis correspondence:

| Node | Lean |
| --- | --- |
| Small nonempty directed preorder I | `(I : Type u) [Preorder I] [Nonempty I] [IsDirectedOrder I]` |
| Three supplied diagrams of commutative rings | `DA DB DC : I ⥤ CommRingCat.{u}` |
| Every stage ring is local | The three dependent `IsLocalRing` instance binders |
| Supplied stage maps f_i and g_i, with transition squares commuting | Natural transformations `ρ : DA ⟶ DB` and `σ : DB ⟶ DC` |
| Supplied transitions respect identity and composition | The `map_id` and `map_comp` fields of each functor; the transition i≤j is `.map (homOfLE h)` |
| Supplied local cocones α_i, β_i, γ_i | `LA`, `LB`, `LC : Cocone ...`, with `hα`, `hβ`, `hγ` |
| Their targets A, B, C are local rings | `IsLocalRing LA.pt`, `IsLocalRing LB.pt`, `IsLocalRing LC.pt` |
| The limit tower A→B→C | `f : LA.pt ⟶ LB.pt`, `g : LB.pt ⟶ LC.pt` |
| Stage tower homomorphisms are local | `hρ` and `hσ` |
| Limit tower homomorphisms are local | `hf` and `hg` |
| Transition homomorphisms are local | `ha`, `hb`, `hc`, for all i≤j |
| Cocone compatibility with transitions | The naturality field of each cocone's `ι` |
| Squares relating stage tower maps and the limit tower commute | `hAB` and `hBC` |
| All three supplied cocones are ring colimits | `hLA : IsColimit LA`, `hLB`, `hLC`, in `CommRingCat` |
| A_i is essentially of finite type over Z | `hZA : ∀ i, Algebra.EssFiniteType ℤ (DA.obj i)` |
| B_i over A_i and C_i over B_i are essentially of finite type | `hABft`, `hBCft` use `RingHom.EssFiniteType` with exactly `(ρ.app i).hom` and `(σ.app i).hom` |
| Adjacent tensor comparisons at i≤j are localizations | `hABtr` and `hBCtr` |
| Adjacent tensor comparisons from each stage to the supplied limit are localizations | `hABlim` and `hBClim` |

For each occurrence `IsTensorLocalizationSquare f r s f'`, the tensor product
is `S ⊗[R] R'`, with algebra structures induced by exactly `f` and `r`.
The definition requires a ring map `φ` and
`∀ x y, φ (x ⊗ₜ[R] y) = s x * f' y`, together with a submonoid W and
`W.IsLocalizationMap φ`. Substitution in `hABtr` gives exactly
b⊗a ↦ b_ji(b) f_j(a); substitution in `hBCtr` gives
c⊗b ↦ c_ji(c) g_j(b). Substitution in `hABlim`, `hBClim` gives
b⊗a ↦ β_i(b) f(a) and c⊗b ↦ γ_i(c) g(b), respectively.
Tensor products carry Mathlib's induced commutative ring structures.
The fields of `Submonoid.IsLocalizationMap`, read in
`Mathlib/GroupTheory/MonoidLocalization/Basic.lean`, are: denominators map to
units, each z satisfies z·φ(w)=φ(x), and φ(x)=φ(y) is killed by some w.
For ring maps the last clause is equivalent to the node's zero-kernel clause
by applying it to x−y. This is also precisely the predicate underlying
`IsLocalization` in `Mathlib.RingTheory.Localization.Defs`.
Locality uses `IsLocalHom`; `IsLocalRing.local_hom_TFAE` in
`Mathlib.RingTheory.LocalRing.RingHom.Basic` identifies it with the node's
inverse-image equality of maximal ideals.

Conclusion clause-by-clause correspondence, in the order of the nine conjuncts:

1. `∀ i, IsNoetherianRing (DA.obj i) ∧ IsNoetherianRing (DB.obj i) ∧ IsNoetherianRing (DC.obj i)`:
   all three supplied stage rings are Noetherian.
2. `∀ i, ((σ.app i).hom.comp (ρ.app i).hom).EssFiniteType`:
   the composite stage map A_i→C_i is essentially of finite type.
3. `∀ i, ∃ P p q, p.FinitePresentation ∧ q.comp p = ... ∧ ∃ W, W.IsLocalizationMap q`:
   the supplied C_i is a localization of a finitely presented A_i-algebra P,
   and its induced A_i-structure is the original composite. The witnesses are
   `P : CommRingCat.{u}`, `p : DA.obj i →+* P`, `q : P →+* DC.obj i`.
   No finiteness is imposed on W.
4. `∀ i j h, IsTensorLocalizationSquare (σ_i.comp ρ_i) a_ji c_ji (σ_j.comp ρ_j)`:
   the composite transition comparison has exactly the formula
   c⊗a ↦ c_ji(c) (g_j f_j)(a) and is a localization.
5. `∀ i, IsTensorLocalizationSquare (σ_i.comp ρ_i) α_i γ_i (g.comp f)`:
   the composite limit comparison has exactly the formula
   c⊗a ↦ γ_i(c) (g f)(a) and is a localization.
6. `∀ x : LA.pt, ∃ i a, (LA.ι.app i).hom a = x`: every element of A has a stage representative.
7. Equality of two base-stage images is an `↔` with
   `∃ k hik hjk, DA.map (homOfLE hik) a = DA.map (homOfLE hjk) b`:
   both directions and a common later stage are required.
8. The analogous representative clause for every `x : LC.pt` gives the assertion for C.
9. The analogous `↔` with the supplied `DC.map` gives equality at a common later stage for C.

There is no existential quantifier over replacement diagrams or cocones in the
conclusion; all comparison maps and elementwise assertions use the supplied
`DA`, `DC`, `LA`, and `LC` directly.

Dependency declarations used, with their recorded sources read:

- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.Cocone`,
  `CategoryTheory.Limits.IsColimit`, supplied by
  `Mathlib.CategoryTheory.Limits.HasLimits`. I read the complete structures in
  `Limits/Cones.lean`, `Limits/IsLimit.lean` and the chosen-colimit interface in
  `Limits/HasLimits.lean`. A supplied cocone uses `IsColimit`, rather than an
  unnecessary replacement by the chosen `colimit`.
- `def-weil-pbc-essentially-finite-type-algebra`: `Algebra.EssFiniteType`,
  `RingHom.EssFiniteType`, `Mathlib.RingTheory.EssentialFiniteness`.
  The latter installs the ring map's exact algebra structure.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` and its pure tensors,
  used with induced ring structures via `Mathlib.RingTheory.TensorProduct.Basic`.
  I read its quotient definition in `LinearAlgebra/TensorProduct/Defs.lean`.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`, equivalent to every ideal being FG.
- `def-weil-pbc-finitely-presented-algebra`: `Algebra.FinitePresentation`,
  through `RingHom.FinitePresentation`, in `Mathlib.RingTheory.FinitePresentation`.
  The former is the recorded finite-polynomial-presentation class; the latter
  applies that exact class to `p.toAlgebra`.

All already-stated proof dependency modules are also imported, without `public`
where they are needed only for the future proof:
`Algebra.FiniteType.isNoetherianRing` (`Mathlib.RingTheory.FiniteType`),
`IsLocalization.isNoetherianRing` (`Mathlib.RingTheory.Localization.Submodule`),
`RingHom.EssFiniteType.comp` (`Mathlib.RingTheory.RingHom.EssFiniteType`),
`Algebra.FinitePresentation.of_finiteType` (`Mathlib.RingTheory.FinitePresentation`,
public already because it is needed in the statement),
`Module.tensorLocalization_tower_transition`
(`WeilConjectures.RingTheory.TensorLocalizationTowerTransition`),
`CategoryTheory.Limits.Concrete.isColimit_exists_rep` and
`CategoryTheory.Limits.Concrete.isColimit_rep_eq_iff_exists`
(`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`), together with
`CommRingCat.FilteredColimits.forget_preservesFilteredColimits`
(`Mathlib.Algebra.Category.Ring.FilteredColimits`). I read their recorded
signatures and docstrings, including the full six-ring comparison theorem.

Edge cases checked before writing:

- The singleton index case and i=j use supplied identities; localization
  comparisons may be isomorphisms, so no strict inequality is imposed.
- A preorder need not be antisymmetric; neither the encoding nor conclusion
  identifies indices that happen to bound one another.
- Noninjective ring transitions are allowed. The equality clauses use a common
  later stage, not equality already at the original stages.
- The empty index type is excluded exactly as in the node. There is no
  independent smaller index universe: both I and the rings use u, as required
  by the project's filtered-colimit size convention. All universes are bound
  explicitly, with `autoImplicit false`.
- The zero ring is excluded by the standard nontrivial-local-ring convention,
  exactly as in the Stacks source. Fields are allowed; maximal ideal zero
  causes no loss in `IsLocalHom`.
- The limits A, B, C may be non-Noetherian and need not be essentially of finite
  type. The conclusions impose these properties only on the stages.
- The denominator submonoids need not be finitely generated or avoid zero
  abstractly; the supplied local target ensures any actual localization has
  nonzero target. Finite presentation applies to P, not to C_i itself.
- P may be taken in u: essentially-finite-type presentations can use a finite
  polynomial algebra over A_i, or the finite type subalgebra supplied by
  Mathlib, so no larger witness universe is required.

Searches actually run, logged by msearch.py in `searches.jsonl`:

- LeanFinder query: "A supplied directed diagram of local ring towers
  essentially finite type over the integers has Noetherian stages and
  composite tensor localization comparisons at transitions and at the colimit".
  Eight results included `RingHom.EssFiniteType.holdsForLocalization`,
  `Algebra.EssFiniteType.isNoetherianRing`,
  `Algebra.FiniteType.isNoetherianRing`, and
  `IsLocalization.isNoetherianRing`; none states the full supplied-diagram result.
  The initial terminal session was lost after interruption, but its completed
  result is present in searches.jsonl at 08:00:37Z.
- LeanFinder follow-up query: "A supplied directed diagram of local ring towers
  essentially finite type over integers has Noetherian stages and composite
  tensor localization comparisons". Eight results additionally included
  `Algebra.EssFiniteType.comp`; again component facts only.
- Loogle query `Algebra.EssFiniteType, IsNoetherianRing`: one result,
  `Algebra.EssFiniteType.isNoetherianRing`, a component of the stagewise result.
- msearch grep query `localization.*(tower|colimit)|EssFiniteType.*(comp|Noetherian)`:
  25 results, including essential-finiteness descent and localization lemmas,
  no full supplied-diagram theorem.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the node id,
  local-tower-collapse names, and tower/Noetherian terms: no occurrence of
  this item or declaration. The NoetherianLocalModelTower family constructs
  towers with additional module data; it does not assert this result for any
  supplied diagram. `rg` for `IsTensorLocalizationSquare`,
  `isTensorLocalizationSquare`, and `local_tower_collapse_noetherian` in
  Mathlib, WeilConjectures, and Sheaf returned no matches before creation.

Validation: `scompile.py Q74 lem-trf-local-tower-collapse-noetherian .../LocalTowerCollapseNoetherian.lean`
passed both sandbox and library-mode compiles (8.4s and 2.4s). Only the requested
statement is postponed. No definition data is supplied by `sorry`; the theorem proof alone is postponed.
Delivery dry-run and push results are recorded by the prescribed wrapper.

## Second reading by Q74

No second worker was started: the dispatched brief explicitly forbids starting
other agents and assigns independent review to the maintainer. The worker reread
the node and final file together: all hypotheses are mapped above, and each of
the nine conclusion conjuncts is accounted for, including both directions of
both equality criteria, all limit comparisons, and the original supplied
cocones. No mismatch or source correction was found. The helper's pure-tensor
formula rules out changing the canonical comparison map. Independent review
remains the maintainer's step.
