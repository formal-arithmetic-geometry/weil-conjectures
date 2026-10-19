## Worker report

Item: lem-cbc-extension-zero-composition. The delivery reuses the existing canonical
natural isomorphism and states its missing coherence laws, with one theorem whose
whole proof is `sorry`. No definition is added and no natural-language statement
is changed. The node's mixed `lean.declarations` records the existing composition
isomorphism alongside the new coherence theorem.

Module: `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`.
New declaration: `AlgebraicGeometry.Etale.openImmersionLowerShriekComp_coherence`.
Existing declaration: `AlgebraicGeometry.Etale.openImmersionLowerShriekComp`, in
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp`.

Clause-by-clause correspondence:

- Coefficients: `Λ : Type (u + 1)` and `[CommRing Λ]`, with coefficient category
  `ModuleCat.{u + 1} Λ`, match the extension-by-zero dependency. No finite or
  nonzero coefficient-ring hypothesis is imposed. The integer case gives the
  usual module encoding of abelian sheaves. The universe follows the established
  étale module-sheaf convention; the schemes are `Scheme.{u}`.
- Composable open immersions: scheme objects and arrows are explicitly quantified;
  each arrow carries exactly `[IsOpenImmersion j]`. Open immersion instances for
  composites and identities are inferred. No quasi-compactness, finiteness,
  separation or nonemptiness hypothesis appears.
- The canonical comparison from iterated extension to composite extension is
  `(openImmersionLowerShriekComp (ModuleCat Λ) j₁ j₂).inv`. Its already-existing
  type is a natural isomorphism from the composite extension to the iterated
  extension, so its inverse has exactly the node's orientation. The existing
  definition constructs it by uniqueness of left adjoints using `upperStarComp`.
  Thus it is the canonical mate specified by the node, not an arbitrary isomorphism.
- Isomorphism: the existing declaration is an `Iso` in the functor category; its
  inverse is automatically an isomorphism on every sheaf `F`. This clause is
  reused, not restated as a tautological `IsIso` conjunct.
- Naturality in `F`: the existing isomorphism is a natural isomorphism of the
  functors on `Sheaf U.smallEtaleTopology (ModuleCat Λ)`. Its `.inv` is a natural
  transformation, with `.inv.app F` the displayed component. There is no
  replacement by an objectwise existence claim.
- Compatibility with an identity on the source is the first conjunct. The
  comparison for `(𝟙 U, j)`, followed by transport along `Category.id_comp`,
  equals the image under `j_!` of the identity comparison on `U`.
- Compatibility with an identity on the target is the second conjunct. The
  comparison for `(j, 𝟙 X)`, followed by transport along `Category.comp_id`,
  equals the identity comparison on `X` evaluated at `j_! F`.
- In those two clauses the identity comparison is Mathlib's
  `Adjunction.leftAdjointIdIso` applied to the recorded extension-by-zero/upper-star
  adjunction and `upperStarId`. It is therefore the canonical mate of the
  inverse-image identity identification, not an unspecified identity isomorphism.
- Three-fold compatibility is the third conjunct. On its left, apply `j₃_!` to
  the comparison for `j₁,j₂`, then compare `j₁ ≫ j₂` with `j₃`, then transport
  along `Category.assoc`. On its right, compare `j₂,j₃` at `j₁_! F` and then
  compare `j₁` with `j₂ ≫ j₃`. Equality is in the category of sheaves on `X`.
  The component notation makes the functor associator definitional.
- The three `eqToHom` terms only identify the extensions along equal scheme
  morphisms. Their small equality proofs use the category unit/associativity
  laws and `Functor.id_obj`; they prove no part of the claimed coherence theorem.

Dependency declarations read and used:

- `def-weil-pbc-extension-by-zero`: full signature and docstring of
  `AlgebraicGeometry.Etale.openImmersionLowerShriek` in
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs` were read.
  Its notation `(j)_!open[ModuleCat Λ]` is used throughout; no private copy exists.
- Proof dependency `lem-weil-pbc-extension-by-zero-adjunction`: the same module's
  `openImmersionLowerShriekAdjunction` and
  `openImmersionLowerShriekUpperStarAdjunction` were read. The latter occurs in
  each canonical identity comparison.
- Proof dependency `def-weil-open-immersion`: Mathlib's `IsOpenImmersion` from
  `Mathlib.AlgebraicGeometry.OpenImmersion`, including its composition instance.
- Proof dependency `def-weil-pbc-composite-adjunction`: Mathlib's `Adjunction.comp`
  and `Adjunction.id`, including the unit/counit formulas, in
  `Mathlib.CategoryTheory.Adjunction.Basic`.
- Proof dependency `lem-weil-pbc-conjugate-iso-unit-equation`: Mathlib's
  `unit_conjugateEquiv_symm` and the conjugation construction in
  `Mathlib.CategoryTheory.Adjunction.Mates`.
- Proof dependency `lem-sc-left-adjoint-composition-iso-associativity`: Mathlib's
  `Adjunction.leftAdjointCompIso_assoc`, full signature and coherence hypothesis,
  in `Mathlib.CategoryTheory.Adjunction.CompositionIso`.

The existing composition module publicly imports the extension-by-zero definition
and upper/lower-star coherence modules. The explicit public CompositionIso import
provides `leftAdjointIdIso` used in the statement and the generic proof ingredients;
Basic and Mates are its transitive imports. The coefficient-category import is
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB`, providing the established
commutative-ring Grothendieck instance. No proof dependency with an available
recorded declaration is omitted from the import closure.

Edge cases checked before writing: empty schemes and empty open subschemes are
included without a nonempty binder; zero sheaves and the zero coefficient ring
remain allowed; either or both arrows may be identity; the three-fold clause
allows identity arrows and empty opens as well. Neither a field nor a
characteristic is fixed. The equations have the same source and target after the
explicit category-law transports. All universe variables and term variables are
bound explicitly, and there is no file-local notation, instance or abbreviation.

Searches (2026-10-15):

- `msearch.py ... leanfinder`, query "composition of extension by zero along open
  immersions natural isomorphism identity associativity": eight unrelated
  structure-sheaf/open-immersion section-map hits, including
  `Scheme.Hom.appIso_inv_app_presheafMap`; no étale coherence theorem.
- `msearch.py ... loogle`, query `"leftAdjointCompIso"`: eight generic adjunction
  results, including `leftAdjointCompIso`, both identity laws and the associativity
  law. They apply to abstract adjunctions and do not directly state this node.
- `msearch.py ... grep`, query
  `leftAdjointCompIso|extension by zero|openImmersionLowerShriekComp`, directory
  `CategoryTheory`: five hits in CompositionIso, giving the generic comparison.
- `msearch.py ... leansearch`, query "composition of extension by zero along open
  immersions of schemes identity associativity": unavailable, Internal Server
  Error; no mathematical verdict drawn from that service.
- `rg` of the source `WeilConjectures` for extension-by-zero names and
  `openImmersionLowerShriek.*(comp|Comp|Id)` found the existing Comp module. Its
  entire file was read: it defines the natural composition isomorphism and an
  inverse-isomorphism comparison, but no identity or triple-coherence laws.
- `grep -rn lem-cbc-extension-zero-composition` in source `WeilConjectures`: no
  match. `rg` in project `lean/Sheaf` found uses of the composition isomorphism,
  but no theorem for its coherence. `rg` for the proposed declaration name in
  upstream names, Mathlib, source and project: no collision.

Validation: server-only `scompile.py`, nice 19, two threads, 60 seconds per file,
passes cleanly (1.5 seconds). The initial guessed coefficient-module import was
corrected to the actual AB module; the initial dependent transports were repaired
using proofs of the standard category equalities. No local compilation was run.
No statement dispute, dependency fault, new node or statement correction remains.

## Second reading by NQ

I independently read the blueprint source named by the node, the complete node
(including its four proof steps), the delivered Lean module and node copy, and
all six statement/proof dependency records. I opened the recorded upstream
extension-by-zero definitions and adjunctions, the entire upstream composition
module, the upper-star identity/composition coherence module, and the Mathlib
adjunction constructions. I also read Stacks etale-cohomology.tex, Definition
03S3 and its following restriction/sheafification paragraphs. There is no
standing Noetherian, separated, quasi-compact or nonempty hypothesis there.
The coefficient convention of the dependency is an arbitrary commutative ring;
Stacks' more general ring formulation does not change that node's convention.

Object/hypothesis/conclusion inventory, matched independently:

- Coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ]`, with no field,
  characteristic, finiteness or nonzero assumption. This is exactly the
  coefficient convention of def-weil-pbc-extension-by-zero. Verdict: matches.
- Schemes and sheaves: `Scheme.{u}` and
  `Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)` use precisely the small
  etale module-sheaf category, not Zariski sheaves, derived objects, or sheaves
  of sets. `universe u` is explicitly bound; the coefficient size follows the
  established dependency convention. Verdict: matches.
- Composable open immersions: the existing `openImmersionLowerShriekComp`
  quantifies `{V U X : Scheme.{u}} (j' : V ⟶ U) (j : U ⟶ X)` with exactly
  `[IsOpenImmersion j'] [IsOpenImmersion j]`. The delivered theorem's third
  conjunct quantifies three such arrows and its first two quantify one with
  an identity. Mathlib's recorded `IsOpenImmersion.comp` supplies composites;
  no extra morphism-property hypothesis is needed. Verdict: matches.
- Canonical comparison: the existing composition definition has type
  `(j' ≫ j)_!open[A] ≅ (j')_!open[A] ⋙ (j)_!open[A]`. Its `.inv.app F` is
  the node's iterated-to-composite arrow. Its body is `leftAdjointUniq`
  between the composite-upper-star adjunction and the single adjunction,
  transported using `upperStarComp.symm`. Thus it is the specified mate,
  with the orientation checked, rather than an arbitrary isomorphism.
  Verdict: matches; reuse is correctly included in `lean.declarations`.
- Invertibility and naturality for every `F`: supplied by that existing
  functor-category isomorphism. Its inverse is a natural transformation and
  every component is invertible. These clauses are not missing merely
  because the new coherence theorem does not restate them. Verdict: matches.
- Source identity: first conjunct compares `c_(id,j),F`, transported along
  `Category.id_comp`, with `j_!.map (e_U.hom.app F)`. Here `e_U` is exactly
  `Adjunction.leftAdjointIdIso` for the recorded shriek/upper-star adjunction
  and `upperStarId`. This is the canonical identity identification in the
  node's third proof step. Verdict: matches.
- Target identity: second conjunct compares `c_(j,id),F`, transported along
  `Category.comp_id`, with `e_X.hom.app (j_!.obj F)`. Its source and target
  coincide with those of the transported comparison. Verdict: matches.
- Three-fold compatibility: third conjunct is
  `j₃_!.map (c_(j₁,j₂),F) ≫ c_(j₁≫j₂,j₃),F ≫ eqToHom (assoc)` equal to
  `c_(j₂,j₃),(j₁_!F) ≫ c_(j₁,j₂≫j₃),F`. Both routes start at
  `j₃_! (j₂_! (j₁_! F))` and end at `(j₁ ≫ (j₂ ≫ j₃))_! F`.
  This is the fourth proof step, with neither a route omitted nor an extra
  conclusion imposed. Verdict: matches.

Dependency review: `openImmersionLowerShriek` really is the same sheafification
of the presheaf left Kan extension, not the shriek for compactifiable maps.
`openImmersionLowerShriekUpperStarAdjunction` transports the recorded restriction
adjunction by `upperStarIsoOpenImmersionRestriction`; hence using upper-star
mates preserves the node's canonical restriction comparison. Mathlib's
`Adjunction.comp`, `unit_conjugateEquiv_symm`, and
`leftAdjointCompIso_assoc` have the recorded signatures and give the stated
proof ingredients. CompositionIso's `leftAdjointIdIso` has type `F ≅ 𝟭 C`
for `F ⊣ G` and `G ≅ 𝟭 C`, confirming the identity orientation in both
conjuncts. All proof ingredients occur in the import closure. There are no
new definition nodes or dependency modules to review.

Edge cases: empty schemes and empty opens remain allowed; all sheaves,
including zero, are quantified; the zero coefficient ring and every
characteristic are allowed. Identity arrows can occur anywhere in the triple.
There is no index set, degree or integer `n`, so empty-index and `n = 0`
restrictions do not arise. All term/universe variables are bound; no independent
undersized test-object universe or additional typeclass constraint occurs.

Independent searches, with different words from the first reading:

- LeanFinder via msearch: `extension by zero functors pseudofunctor composition
  unit pentagon` returned eight generic pseudofunctor results (WithInitial,
  WithTerminal, Functor.toPseudoFunctor and related declarations), not this
  etale comparison's coherence statement.
- Loogle via msearch: `"leftAdjointIdIso"` returned the construction and its
  hom, inv and conjugation formulas. These are the generic identity ingredients,
  not a duplicate of this etale statement.
- LeanSearch via msearch: `canonical composition of extension by zero sheaf
  functors identity coherence` was unavailable (Internal Server Error). No
  mathematical conclusion is drawn from this unavailable service.
- msearch grep: `shriek.*[Cc]omp|[Cc]omp.*shriek` returned no hits.
- Direct `rg` on Mathlib, upstream WeilConjectures and project lean/Sheaf for
  `lowerShriekComp`, `LowerShriekComp`, `extensionByZero.*[Cc]omp`, and
  `extension.*zero.*[Cc]ompos`, followed by a narrower search for
  `openImmersionLowerShriekComp` and identity/associativity/coherence suffixes,
  found the reused Comp definition, its derived-category image and applications.
  The entire Comp module contains only the composition and inverse-isomorphism
  constructions. Other hits concern compactifiable/derived or pro-etale shriek,
  so they do not state this node. No duplicate etale coherence statement found.

No H3/H4 mismatch was found, and no Lean or node change was needed. The theorem
is left as one named `sorry`; there is no hollow definition or extra proved
lemma. The three inline equality proofs only transport along category laws.
The module and declaration docstrings carry the source and blueprint marker;
the declaration docstring follows all four node proof steps. The recorded
`lean.statement` is verbatim the theorem signature, and the file has no local
notation/instance/private copy. Second reading changed only this review report.

Validation by the second reader: signature equality and 100-character width
checked mechanically. The sole delivered module compiled cleanly with scompile.py
on the server (1.5 seconds, nice 19, two threads, 60-second limit); no warning
or error was reported. No local compiler or global build was used.
