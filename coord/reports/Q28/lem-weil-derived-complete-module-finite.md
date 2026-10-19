## Worker report

The module `lean/Sheaf/RingTheory/DerivedCompleteModuleFinite.lean` states
`ModuleCat.finite_and_completion_bijective_of_isDerivedComplete`, with its entire
proof postponed as `by sorry`. It introduces no definitions or helper assertions.
The module and theorem docstrings cite Stacks Tag 09BA, specialized to a complete
ring. The theorem docstring carries all seven proof steps of the node, including
the multiplication-tower criterion, cokernel closure, finite-free argument,
residue-generator argument, successive quotients, descending derived Nakayama,
and the ordinary-completeness conclusion.

Hypothesis and clause correspondence:

- A commutative Noetherian ring is `{A : Type u} [CommRing A]
  [IsNoetherianRing A]`. `I : Ideal A` is the stated arbitrary ideal.
- The assumed canonical isomorphism from the ring to its completion is
  `hA : Function.Bijective (AdicCompletion.of I A)`. This is the canonical
  residue-sequence map, not an arbitrary equivalence. Its underlying function
  agrees with that of the canonical ring homomorphism, so bijectivity says
  precisely that this canonical map is an isomorphism.
- An arbitrary A-module is `(M : Type v) [AddCommGroup M] [Module A M]`.
  The ring and module universes `u` and `v` are independent and explicitly bound.
- The hypothesis of derived completeness is
  `hM : ModuleCat.IsDerivedComplete I (ModuleCat.of A M)` (written with the
  current namespace's unqualified `IsDerivedComplete` in the file). The recorded
  definition unfolds to derived completeness of `M[0]` in D(A); it universally
  quantifies over the multiplication towers and their derived limits. It is not
  ordinary adic completeness or a coefficient-sheaf predicate.
- `[HasDerivedCategory.{w} (ModuleCat.{v} A)]` supplies the abstract derived-category
  model required by the recorded predicate. It is categorical infrastructure,
  with independent explicit `w`, and adds no mathematical completeness condition.
- Finiteness of the residue as an A/I-module is exactly
  `hfinite : Module.Finite (A ⧸ I) (M ⧸ (I • ⊤ : Submodule A M))`.
  The quotient-ring module instance is Mathlib's canonical one from
  `Mathlib.Algebra.Module.Torsion.Basic`; no action is supplied as extra data.
- The first conclusion `Module.Finite A M` is finite generation over A.
- The second conclusion `Function.Bijective (AdicCompletion.of I M)` says that
  the specified canonical A-linear map into the compatible residue sequences is
  an isomorphism. `AdicCompletion I M` is the subtype of families in
  `M ⧸ (I ^ n • ⊤ : Submodule A M)` compatible under `transitionMap`, with
  componentwise operations. Mathlib indexes by n ≥ 0; the extra n = 0 component
  is the zero quotient M/M and uniquely determined, so this is precisely the
  node's inverse limit indexed by n ≥ 1. No additional conclusion is asserted.

Statement dependency declarations used, read with signatures and docstrings:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` in
  `Mathlib.RingTheory.Noetherian.Defs`, the condition that all ideals are finite.
- `def-weil-pbc-adic-completion`: `AdicCompletion` and `AdicCompletion.of` in
  `Mathlib.RingTheory.AdicCompletion.Basic`. Read the actual compatible-family
  subtype, componentwise module operations, and canonical map. The equivalence
  `AdicCompletion.of_bijective_iff` identifies bijectivity with `IsAdicComplete`.
- `def-weil-point-derived-complete-module-complex`:
  `ModuleCat.IsDerivedComplete` and `DerivedCategory.IsDerivedComplete` in
  `Sheaf.RingTheory.DerivedCompleteModuleComplex`. The live server source was
  checked using `scompile.py --source` and agrees with the shared checkout.
- `def-weil-finitely-generated-module`: `Module.Finite` in
  `Mathlib.RingTheory.Finiteness.Defs`, i.e. the top submodule is finitely generated.

All recorded proof-dependency modules are imported. Besides the statement modules,
these are `Sheaf.CategoryTheory.Triangulated.DerivedLimitExistence`
(`CategoryTheory.exists_isDerivedLimit_and_iso` and
`CategoryTheory.derivedCategory_countableProducts_and_towerLimit`),
`WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`
(`CategoryTheory.IsDerivedLimit`, read via the live `--source` wrapper),
`Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
(`DerivedCategory.HomologySequence.exact₁`, `exact₂`, `exact₃`, and
`DerivedCategory.isIso_iff`), and `Sheaf.RingTheory.FiniteModuleComplete`
(`finite_module_complete_over_complete_noetherian`). Proof-only imports use
`import`, not `public import`; no import is omitted for a cycle.

Edge cases checked before drafting:

- I = 0: completion is canonically M, derived completeness imposes no restriction,
  and the finite-residue hypothesis is precisely finite generation of M.
- I = A: bijectivity of the ring-completion map forces A to be the zero ring;
  all unital A-modules are zero. The statement allows this case.
- M = 0 and the zero ring: the canonical completion maps are bijective and
  finite generation includes the empty family of generators.
- No proper-ideal, locality, nonzero-ring, torsion-freeness, boundedness, or
  ordinary-Hausdorffness hypothesis has been added. In particular, derived
  completeness has not been replaced by the stronger ordinary-completeness
  hypothesis needed in the nearby `Module.finite_and_span_eq_top_of_adicComplete`.

Searches made (2026-10-16):

- `msearch.py ... leanfinder "A derived complete module over a complete Noetherian
  ring with finitely generated residue modulo an ideal is finitely generated"`:
  eight hits, including `IsAdicComplete`, `IsPrecomplete`, ordinary completion,
  `AdicCompletion.flat_of_isNoetherian`, and the completion tensor-product theorem.
  None is this derived-complete finiteness criterion.
- `msearch.py ... loogle "IsAdicComplete, Module.Finite"`: zero hits.
- `msearch.py ... grep "IsDerivedComplete|derived.?complete|09BA" RingTheory`:
  zero Mathlib hits.
- `msearch.py ... leansearch "Derived complete modules with finite residue over a
  complete Noetherian ring are finite"`: eight hits, concerning finiteness and
  Noetherianity or completion of an already finite module; no exact match.
- `rg -n 'IsDerivedComplete|derived.?complete|09BA'` in upstream WeilConjectures
  and shared `lean/Sheaf`: found the recorded module-complex predicate and
  sheaf/complex derived-completeness material, but no finite-residue theorem.
- `grep -rn 'lem-weil-derived-complete-module-finite'` in upstream
  WeilConjectures: no hits.
- The nearby `Sheaf.RingTheory.FiniteOverCompleteRing` theorem assumes ordinary
  Hausdorffness, which is not given here; its full signature and docstring were
  read and it is not an exact existing match.

Source checked: the local Stacks source tree is absent on this machine, so read
[Stacks Tag 09BA](https://stacks.math.columbia.edu/tag/09BA) directly. It states
finiteness over the completed ring and ordinary completeness; the node's existing
hypothesis identifies that ring with A. No statement correction is needed.
No disputed statement, dependency repair, new node, or changed dependency list.

Validation: `scompile.py Q28 lem-weil-derived-complete-module-finite
lean/Sheaf/RingTheory/DerivedCompleteModuleFinite.lean` succeeded for both the
sandbox and library module forms (37.3 s and 4.5 s), without diagnostics.
All variables and universes are explicitly bound and all Lean lines have at most
100 characters. Only the item's `lean` field differs from the original node.

## Second reading by Q28

I independently read the item node and the sandbox module side by side, then
opened all four statement-dependency records and their actual declarations.
The live `scompile.py --source Sheaf.RingTheory.DerivedCompleteModuleComplex`
output agrees with the shared source. I also read the completion definition and
canonical map in Mathlib, its canonical quotient-ring action, and the nearby
ordinary-completeness finiteness theorem. No mathematical or interface mismatch
was found. The Lean module and node signature are unchanged; this section is the
only review amendment.

Source check: the local Stacks .tex checkout is absent. I read Tag 09BA at
https://stacks.math.columbia.edu/tag/09BA and fetched the actual
`more-algebra.tex` from
https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex,
reading `lemma-derived-complete-finite` and the introduction of its containing
section, `section-derived-completion-noetherian`. The source assumes an ideal in
a Noetherian commutative ring, a derived-complete module and finite residue. Its
conclusions are ordinary completeness and finiteness over the completed ring.
The node explicitly specializes to the case in which the canonical map from A
to that completed ring is an isomorphism. This specialization is exactly what
the Lean states; no source-wide locality, properness of the ideal, characteristic,
or additional module condition has been omitted. No statement correction or
citer audit is needed.

Object, hypothesis and conclusion checklist (each verdict: exact):

1. Object A and its commutative ring structure: `{A : Type u} [CommRing A]`.
   Noetherianity: `[IsNoetherianRing A]`. The recorded Mathlib abbreviation
   `IsNoetherianRing` is `IsNoetherian A A`, equivalently finite generation of
   every ideal. These are the ring and hypothesis of the node.
2. Arbitrary ideal of this ring: `(I : Ideal A)`. There is no properness,
   principal-ideal, finite-choice-of-generators or Jacobson-radical assumption.
3. Canonical isomorphism from A to its I-adic completion:
   `hA : Function.Bijective (AdicCompletion.of I A)`. The actual `of` definition
   sends an element to its quotient classes, not to an arbitrarily chosen
   isomorphism. It is linear, and for A itself is the underlying canonical ring
   map, so bijectivity expresses exactly the asserted isomorphism.
4. Object M and its A-module structure: `(M : Type v) [AddCommGroup M]
   [Module A M]`. There is no finiteness, separatedness, torsion or nonzero
   assumption on M hidden in these binders. The module and ring universes are
   independent.
5. Derived completeness of M[0]: `hM : IsDerivedComplete I (ModuleCat.of A M)`.
   The recorded `ModuleCat.IsDerivedComplete` is precisely
   `DerivedCategory.IsDerivedComplete I
   ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj M)`.
   The latter quantifies over every f in I and every Roos derived limit of the
   constant multiplication-by-f tower and asks that it be zero. It is the
   node's module-complex notion, not the coefficient-sheaf predicate and not
   ordinary adic completeness. `[HasDerivedCategory.{w} (ModuleCat.{v} A)]`
   supplies the derived-category model used by this recorded dependency, with
   w explicitly independent; it adds no algebraic assumption on A, I or M.
6. Finite residue as an A/I-module:
   `hfinite : Module.Finite (A ⧸ I) (M ⧸ (I • ⊤ : Submodule A M))`.
   The denominator is IM. Mathlib's instance in
   `Mathlib.Algebra.Module.Torsion.Basic` comes from I annihilating this quotient;
   its `Quotient.mk_smul_mk` computes the action as the original action reduced
   modulo I. Hence this is the canonical A/I-action with no extra action datum.
   `Module.Finite` is the recorded notion of finite generation (the top
   submodule is FG), not finiteness of the underlying set.
7. First conclusion, M finite over A: `Module.Finite A M`.
8. Second conclusion, the specified canonical M-completion map is an
   isomorphism: `Function.Bijective (AdicCompletion.of I M)`. Its codomain is
   literally Mathlib's subtype of compatible families in
   `M ⧸ (I ^ n • ⊤ : Submodule A M)`, with componentwise operations, and `of`
   takes the residue of the given m in each component. Bijectivity of this
   linear map expresses exactly the module-isomorphism clause. The conjunction
   includes both conclusions, with no additional generator statement or
   altered quantifier order.

Edge cases: I = 0 reduces the residue hypothesis to finite generation of M and
completion to M; no nonempty generator family is required. I = top forces A to
be the zero ring under hA and allows its zero modules. M = 0 and the zero ring
are admitted. Completion is indexed by all natural numbers in Mathlib: the
n = 0 quotient M/M is zero and uniquely determined, so including this component
does not change the inverse limit over n >= 1. The degree-zero single functor
is correctly used for M[0]. All characteristics are allowed. There is no scheme
or separate finite index object in the statement; empty-scheme cases do not
arise. Explicit universes u, v, w introduce no equality or smallness requirement.
All variables and universe names in the signature are bound.

Independent duplicate searches, using alternative terminology, on 2026-10-16:

- LeanFinder via `msearch.py`: "Contramodule Nakayama lemma: a module complete in
  the derived sense over a complete ring is finitely generated when its
  reduction is finite". Eight hits concern ordinary completeness or completion
  of an already finite module; no theorem gives the item.
- Loogle via `msearch.py`: `Module.Finite, AdicCompletion.of`. One hit,
  `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_symm_of`, assumes
  finiteness and describes a tensor comparison; it is not this statement.
- LeanSearch via `msearch.py`: "Nakayama finiteness criterion for contramodules
  over adically complete Noetherian rings". Eight hits: ordinary Nakayama,
  ordinary precompleteness/Hausdorffness, Noetherian finiteness, and tensor
  completion identities; no exact match.
- `rg` in Mathlib/RingTheory, upstream WeilConjectures, and shared
  lean/Sheaf/RingTheory for `contramodule`, Nakayama, and derived-completeness
  variants found the recorded completeness definition and closure results,
  plus ordinary Nakayama material. The full signature of
  `Module.finite_and_span_eq_top_of_adicComplete` in
  `Sheaf.RingTheory.FiniteOverCompleteRing` requires `[IsHausdorff I M]`, so
  it is not an existing rendition of this derived-completeness criterion.
  Searches by the proposed declaration and blueprint id found no duplicate.

There are no new nodes or dependency modules to review (H12/H13). The delivered
file defines no data and introduces no hollow notion (H5); its sole theorem
body is `by sorry` (H6). Module and declaration docstrings contain the source
place and the correct blueprint tag. I checked all seven proof-docstring steps
against the node: multiplication-tower computation, cokernel closure, finite
free source, lifted residue generators, successive quotients, descending
Nakayama, and finite-module ordinary completeness are all present (H8).
The canonical operations remain those of the recorded dependencies (H4).
Imports include the statement dependencies and all recorded proof-dependency
modules. There is no file-local notation, instance, private declaration, let or
hidden show/from expression in the statement. Maximum Lean line length is 87.
Whitespace normalization of the signature equals `lean.statement` verbatim.

Validation: the prescribed `scompile.py Q28
lem-weil-derived-complete-module-finite
lean/Sheaf/RingTheory/DerivedCompleteModuleFinite.lean` succeeded, compiling
sandbox and library forms separately in 52.0 s and 3.9 s respectively, with no
diagnostics. No additional compilation is required because the module was not
changed after that successful check.
