## Worker report

The module `Sheaf.AlgebraicGeometry.FormalCompletionFullyFaithfulProper` states
`AlgebraicGeometry.formalCompletion_map_bijective_of_proper`, with its sole proof
`sorry`. It states the Hom-set formulation of full faithfulness in the node, using
the already landed completion functor. No definition, additional node, dependency
module, or statement correction is needed.

Hypotheses and clauses, individually matched:

- A commutative ring A: `{A : Type u} [CommRing A]`.
- A Noetherian: `[IsNoetherianRing A]`, the recorded Mathlib notion that every
  ideal is finitely generated.
- An ideal I in A: `(I : Ideal A)`.
- A complete with respect to I, including separatedness: `[IsAdicComplete I A]`.
  Mathlib's `AdicCompletion.of_bijective_iff` identifies this with bijectivity
  of the canonical map to the inverse limit of A/I^n.
- A scheme X and a proper morphism to Spec A:
  `{X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]`.
  The common universe permits all the rings and schemes after universe enlargement.
- The ideal sheaf I O_X is
  `(Scheme.IdealSheafData.ofIdealTop
  (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f`.
  `ΓSpecIso.inv` transports I from A to Γ(Spec A,O); `ofIdealTop`
  constructs its associated quasi-coherent ideal sheaf, and the dependency's
  `comap f` is its extension along f. This uses the same expression as the
  landed `Sheaf.AlgebraicGeometry.QuotientBaseChangeIdeal` statements.
- The completion functor Coh(O_X) → Coh(X,I O_X): the existing `completion`.
  Its Noetherian instance argument is supplied explicitly by
  `isNoetherian_of_locallyOfFiniteType f`, derived from properness and the
  Noetherian base; no additional hypothesis on X is introduced.
- Arbitrary coherent G and F: `(G F : CoherentModules X)`, the existing full
  subcategory defined by `RingedSpace.IsCoherent X.toRingedSpace`.
- The map Hom(G,F) → Hom(G^,F^), u ↦ u^: the lambda
  `fun v : G ⟶ F ↦ (@completion X ... ...).map v`.
  The source full subcategory has the original module Hom sets, and the
  target has natural transformations, i.e. compatible families of maps
  of the quotient modules. The existing completion's map is exactly reduction
  modulo each positive ideal power, not an unspecified comparison map.
- Bijectivity, hence full faithfulness for all coherent pairs:
  `Function.Bijective` applied to that lambda. Both injectivity and surjectivity
  of precisely the named map are asserted.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete` (and its
  separated/precomplete fields).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Sheaf.AlgebraicGeometry.CoherentFormalModule`: `AlgebraicGeometry.CoherentModules`,
  `AlgebraicGeometry.CoherentFormalModule`, `AlgebraicGeometry.completion`,
  `formalCompletionSystem`, `formalCompletionMap`, with the actual quotients
  `formalModuleQuotient` and reductions `formalModuleQuotientMap`.
- `Sheaf.AlgebraicGeometry.Coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent`,
  used through `CoherentModules` (transitive import, not an unused direct import).
- `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`:
  `AlgebraicGeometry.Scheme.IdealSheafData.comap`.
- The Noetherian consequence uses
  `WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian`:
  `AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType`.
  `Scheme.IdealSheafData.ofIdealTop` and `Scheme.ΓSpecIso` are existing Mathlib
  constructions, not privately redeclared notions.

Edge cases checked before writing:

- I = 0: every positive-level quotient is F, so completion is the constant
  compatible system and its Hom map is bijective, as asserted.
- I = A: adic separatedness forces A to be the zero ring. Spec A is empty;
  a morphism to it forces X empty. Thus the statement does not accidentally
  assert full faithfulness of the zero completion on a nonempty scheme.
- A the zero ring and X empty are allowed: no nontriviality or nonempty
  assumptions were added, and all module Hom sets are singleton.
- F or G zero is allowed by the full-subcategory object binders.
- The formal category uses op n for level n+1; no extra level-zero object or
  hypothesis is imposed. Morphisms are full natural transformations, so all
  compatibility conditions remain those of the recorded definition.
- No affine hypothesis on X, connectedness, residue characteristic, or
  field assumption is introduced. No `let`, hidden `show`, file-local
  notation, or locally declared instance is used in the signature.

Searches made for the existing statement:

- `msearch.py leanfinder`, query “Completion functor on coherent modules of a
  proper scheme over a complete Noetherian ring is fully faithful”: eight
  hits, on constant condensed modules or the fully faithful forgetful
  functor `Scheme.Modules.toPresheafOfModules`; none is adic completion.
- `msearch.py loogle`, query `CategoryTheory.Functor.FullyFaithful, IsAdicComplete`:
  zero hits.
- `msearch.py grep`, query
  `completion.*[Ff]aithful|[Ff]aithful.*completion|formal.functions`, subdirectory
  `AlgebraicGeometry`: zero hits.
- `msearch.py leansearch`, query “Fully faithful completion of coherent
  sheaves on proper schemes over adically complete Noetherian rings”:
  service unavailable (Internal Server Error); this is a recorded service
  failure, not negative mathematical evidence.
- `rg -n 'formal.*[Ff]aithful|completion.*[Ff]aithful|<item id>'` on the source
  `WeilConjectures` and project `lean/Sheaf`: no matching theorem; broad
  matches mention unrelated faithful flatness of ring completions.
- `rg` for `completion`, `ofIdealTop`, and `isNoetherian_of_locallyOfFiniteType`
  found the shared completion definition, the ideal expression in
  `QuotientBaseChangeIdeal`, and the exact Noetherianity theorem used here.

Source check: the local Stacks TeX checkout is absent on this machine. Read
[Stacks Lemma 0883](https://stacks.math.columbia.edu/tag/0883) directly.
It has exactly the stated Noetherian, adic-completeness and properness
hypotheses, and its proof uses coherent internal Hom, Lemma 0882 and formal
functions in degree zero. The declaration docstring includes all five steps
of the node's proof and their named dependencies.

No statement dispute or node fault was found. The only pending proof is the
stage-2 theorem above. Server compilation completed cleanly in 2.3 seconds (exit code 0), without
warnings. `deliver2.py R1 lem-weil-pbc-formal-completion-fully-faithful-proper
--no-push` printed OK: compilation and preflight pass except for the second
reading, which the next worker writes. Nothing was pushed.


## Second reading by R1

Independent second reading against the original DAG node, the sandbox signature,
all six statement-dependency nodes and their declarations. Verdict: the Lean
states exactly the node; no repair to the declaration or node was needed.

Source checked independently: the local Stacks checkout is absent. Read the
upstream `coherent.tex` at
https://raw.githubusercontent.com/stacks/stacks-project/master/coherent.tex,
labels `lemma-fully-faithful` (0883) and `section-coherent-formal` (0EHN),
and the rendered https://stacks.math.columbia.edu/tag/0883.
The section assumes a Noetherian scheme and a quasi-coherent ideal; these follow
here from the Noetherian base, properness and extension of the base ideal.
No missing ambient hypothesis was found.

Objects, hypotheses and conclusions, item by item:

- Object A, a commutative ring: `{A : Type u} [CommRing A]`. Pass; no field,
  domain, nontriviality or characteristic condition.
- A Noetherian: `[IsNoetherianRing A]`. Pass. Opened Mathlib's declaration
  in `RingTheory/Noetherian/Defs.lean` and its ideal-finite-generation equivalence;
  it is the recorded `def-weil-pbc-noetherian-ring` notion.
- Ideal I of A: `(I : Ideal A)`. Pass; no restriction on the ideal.
- A complete and separated for the I-adic filtration: `[IsAdicComplete I A]`.
  Pass. Opened `AdicCompletion/Basic.lean`: the class extends `IsHausdorff`
  and `IsPrecomplete`, and `AdicCompletion.of_bijective_iff` gives exactly the
  canonical-limit-map formulation in `def-weil-pbc-adically-complete-ring`.
- Scheme X and proper f to Spec A:
  `{X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]`. Pass.
  Opened `Morphisms/Proper.lean`: separated, universally closed and locally
  finite type; universal closedness supplies quasi-compactness, hence finite
  type as in `def-weil-proper-morphism`. No affine assumption on X.
- Extended quasi-coherent ideal I O_X:
  `((Scheme.IdealSheafData.ofIdealTop
  (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)`. Pass.
  Opened `IdealSheaf/Basic.lean`: `ofIdealTop` extends an ideal of global
  sections to affine opens by restriction. `ΓSpecIso.inv` transports I from
  A into those sections. Opened `IdealSheaf/Functorial.lean`: `comap` is the
  kernel ideal of the pulled-back closed subscheme, precisely the extension
  in `def-nagata-extended-ideal`, including nilpotent structure.
- Category of coherent modules: `(G F : CoherentModules X)`. Pass.
  Opened `Coherent.lean`: `RingedSpace.IsCoherent` is finite type plus finite
  type kernels of all maps from finite free modules on all opens, matching
  `pqf-def-coherent`. `CoherentModules` is its full subcategory of X.Modules.
- Target category and completion: `@completion X
  (isNoetherian_of_locallyOfFiniteType f) ...`. Pass. Opened
  `CoherentFormalModule.lean` in full: its category is the full subcategory of
  inverse-system functors satisfying coherence, annihilation by I^(n+1), and
  the specified quotient-transition isomorphism. Morphisms are compatible
  families, not arbitrary maps. Opened the Noetherian consequence's signature:
  only locally finite type, quasi-compactness and a Noetherian target are
  needed; all follow here. It is a derived proof argument, no added binder.
- Specific map u ↦ u^: the lambda `fun v : G ⟶ F ↦ (...).map v`. Pass.
  Followed `completion` through `formalCompletionFunctor`,
  `formalCompletionMap`, `formalModuleQuotientMap` and `formalModuleQuotient`.
  The objects are actual cokernels of ideal-product inclusions and maps are
  cokernel descents of v followed by the quotient projection. Also opened
  shared `idealModuleProduct`, `idealSheafPower`, `toModules` and `toModulesι`:
  they are actual multiplication images, recursively defined powers and the
  kernel ideal subsheaf. None supplies unknown data via sorry.
- Bijectivity on Hom(G,F) for every coherent pair: `Function.Bijective`
  of that lambda. Pass: both injectivity and surjectivity of the named
  completion map, equivalent to full faithfulness. F and G are universally
  quantified after the base and morphism, in the stated direction G → F.

Edge cases: I = 0 gives constant systems up to their quotient isomorphisms.
I = top forces A to be zero by separatedness, hence Spec A and X empty;
there is no false zero-completion claim for nonempty X. Zero rings, empty X,
and zero coherent modules are allowed. The index op 0 means positive level 1;
adding level 0 would only add its forced zero object and is unnecessary.
There is no empty-family hypothesis, characteristic restriction or hidden
nonemptiness condition. Universe u is arbitrary and shared by Scheme, Spec,
module carrier and their established dependency APIs; no quantifier over a
smaller independent universe, or finite universe bound, is introduced.

Independent searches with different wording:

- `msearch.py leanfinder`: “Grothendieck existence theorem morphisms of coherent
  sheaves recover uniquely from all adic quotients”. Eight hits: sheaf Hom
  extensionality and covering/sheafification results, none this theorem.
- `msearch.py loogle`: `IsAdicComplete, Function.Bijective`. Two hits:
  `AdicCompletion.of_bijective` and `AdicCompletion.of_bijective_iff`.
  Inspected their returned types: module-to-adic-completion maps, not Hom sets
  of coherent sheaves on a proper scheme.
- `msearch.py grep`: `Grothendieck|completion.*[Bb]ijective|[Bb]ijective.*completion`.
  Returned ring completions, infinite-place completions and generic
  Grothendieck material; none the statement.
- Direct rg across Mathlib, source WeilConjectures and project lean/Sheaf:
  `grothendieck.*exist|fully.?faithful.*(adic|complet)|
  (adic|complet).*fully.?faithful|formalCompletion_map_bijective_of_proper`
  (case insensitive). Only unrelated Grothendieck comments and the landed
  algebraization citation; no existing declaration for this statement.

No new definition nodes, dependency modules or statement correction are in
this delivery, so H12/H13 and correction-citer review have no added objects
to check. H5/H6: the module introduces no definitions and exactly one named
statement, whose proof is `by sorry`; dependency data constructions checked
above are not hollow. H8: module and theorem docstrings name 0883 and the
blueprint id; the theorem docstring records all five DAG proof steps, including
the identification of the composite with completion on maps. H9: bound universe
and variables, standard namespace, no private notation, no hidden let/show,
no extra conjunct, and all lines within 100 characters. Node lean.statement
was checked by exact string equality with the file's signature.

Mismatches found: none. Changes: appended this independent reading only;
kept the worker report, Lean module and node intact.
