## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentFormalModuleIsomorphismLocal` states
`AlgebraicGeometry.coherentFormalModule_isIso_of_isIso_restrict`, with only a `sorry`
proof. No definition, new node, dependency module, or statement correction is needed.

Hypotheses and clauses, matched individually:

- The scheme X is `{X : Scheme.{u}}`. `[IsNoetherian X]` is exactly locally
  Noetherian plus quasi-compact: Mathlib's class extends `IsLocallyNoetherian X`
  and `CompactSpace X`, with no separatedness condition.
- The quasi-coherent ideal I is `(I : X.IdealSheafData)`, the representation
  used by the dependency's recorded `CoherentFormalModule`. Its affine ideal
  data and localization compatibility encode the quasi-coherent ideal sheaf.
- The arbitrary open cover is `{J : Type v} (U : J → X.Opens)` and
  `(hU : iSup U = ⊤)`. It is neither assumed finite nor nonempty.
- The systems F and G are `{F G : CoherentFormalModule X I}`. This uses the
  full coherent adic inverse-system definition, not arbitrary independent modules.
- The compatible family alpha is `(α : F ⟶ G)`. Full-subcategory morphisms have
  underlying natural transformation `α.hom`; its component is `α.hom.app (op n)`.
  Here `n : ℕ` represents the paper's positive level n+1, including level 1.
- Restriction to U_j is `(Scheme.Modules.restrictFunctor (U j).ι).map`.
  Mathlib's actual open-immersion restriction has components the original
  components on opens contained in U_j, with the canonical identification of
  the restricted structure sheaf. It is restriction, not tensor pullback.
- The local hypothesis `hα` quantifies over every j and every positive level
  (encoded by every natural n) and asserts `IsIso` of this restricted map.
- The conclusion `IsIso α` asserts the isomorphism in Coh(X,I).
- `∃ β : G ⟶ F` gives the actual compatible inverse morphism.
  `α ≫ β = 𝟙 F` is beta-circle-alpha = id_F, and
  `β ≫ α = 𝟙 G` is alpha-circle-beta = id_G.
- For each n the conclusion supplies `e : F.obj.obj (op n) ≅ G.obj.obj (op n)`
  with `e.hom = α.hom.app (op n)` and `e.inv = β.hom.app (op n)`.
  These two equalities express precisely that each alpha_n is an isomorphism
  of O_X-modules and beta_n is alpha_n's inverse. An existential isomorphism
  avoids needing an instance binder or a let in the signature; it imposes no
  extra choice or hypothesis.

Dependency declarations read and used:

- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`, and its `IsNoetherian` extension.
  The recorded class has the affine Noetherian rings characterization, equivalent
  to the node's affine-cover formulation by its recorded characterization lemmas.
- `def-weil-pbc-coherent-formal-module`:
  `Sheaf.AlgebraicGeometry.CoherentFormalModule`,
  `AlgebraicGeometry.CoherentFormalModule` and `IsCoherentFormalModule`.
  Read the definition and docstrings: objects are full-subcategory objects of
  `ℕᵒᵖ ⥤ X.Modules`, with coherent terms, annihilation, and quotient-transition
  isomorphisms. Natural transformations give the compatible maps.
- `def-weil-sheaf-of-modules-category`:
  `Mathlib.AlgebraicGeometry.Modules.Sheaf`, `AlgebraicGeometry.Scheme.Modules`.
  Read its definition and `restrictFunctor`; it is the same module category used
  in the formal-module dependency. All are available through the one import.

Source check: this machine has no `literature/stacks-project/coherent.tex`.
Opened the primary source https://stacks.math.columbia.edu/tag/087X (Lemma 30.23.2).
It assumes a Noetherian scheme and quasi-coherent ideal, states locality of exactness
and exact open restriction, and constructs kernels/cokernels locally. The item's
three-step derived locality-of-isomorphisms argument is preserved in the docstring:
glue local inverses using the cited gluing lemma, conjugate naturality, then use
componentwise composition. No mathematical assertion from the item is changed.

Edge cases checked before writing: the empty scheme and an empty covering are allowed
(the cover equality can then hold); modules on the empty space have only trivial maps.
Empty members of a cover impose no extra nontrivial condition. Arbitrary infinite
coverings and independent index universes are allowed, since no categorical limit is
taken over J. The level n=0 means positive level 1, not an extra level-zero condition.
The zero ideal (constant systems), unit ideal (zero systems), and zero objects do not
invalidate the statement. No characteristic or base ring restriction is added.

Searches (2026-10-11), all with item-scoped msearch.py:

- `leansearch`: "isomorphism of inverse systems of coherent modules detected locally
  on an open covering": service unavailable (Internal Server Error); recorded as
  unavailable, not evidence of absence.
- `leanfinder`: "morphism of coherent formal modules isomorphism on open cover":
  eight hits, notably `Scheme.Modules.Hom.isIso_iff_isIso_app`, `inv_app`, and
  `PresheafOfModules.isoMk`; these concern single sheaves or presheaves and do not
  state the coherent-formal inverse-system assertion with this cover hypothesis.
- `loogle`: "CategoryTheory.IsIso, Scheme.Modules, open cover": parser rejected
  the natural-language part (expected `in`), no successful result from this query.
- `grep`: `CoherentFormalModule|isIso.*restrict|isIso.*cover` under Mathlib's
  AlgebraicGeometry: restriction-adjunction and scheme-morphism isomorphism tools,
  no coherent-formal-module locality theorem.
- `rg` on WeilConjectures and lean/Sheaf for `CoherentFormalModule`,
  `coherent_formal.*[Ii]so`, and `isIso.*restrict`: only the dependency supplies
  coherent formal modules; the other matches concern scheme morphisms, individual
  module stalks, or étale/pro-étale restriction. No same theorem found.
- `rg` for the exact item id in WeilConjectures: no match.

Validation: server scompile.py compiled this module in 2.0 seconds, exit code 0,
with no warnings. All universes and variables are explicitly bound. Only the theorem
proof is `sorry`, and the module docstring and theorem docstring name the node/source.

- Follow-up valid `loogle` query:
  `AlgebraicGeometry.Scheme.Modules.Hom.isIso_iff_isIso_app`: one exact-name hit,
  signature `IsIso φ ↔ ∀ U, IsIso (Scheme.Modules.Hom.app φ U)`.
  This is the all-opens sections criterion for one module map, not the current
  open-cover criterion for compatible coherent formal systems.

Delivery dry run: deliver2.py --no-push printed OK; the module compiles and the
preflight passes except for the independent second reading, which the second reader
must write. No second-reading section or delivery push was made by this worker.

## Second reading by K1

The node introduces the following data and clauses, matched against
`AlgebraicGeometry.coherentFormalModule_isIso_of_isIso_restrict`:

- A scheme `X` with `[IsNoetherian X]`; this is Mathlib's locally Noetherian and
  quasi-compact class, matching the node's expansion of Noetherian.
- A quasi-coherent ideal `I : X.IdealSheafData`, rendered by the explicit `I`
  argument and used in `CoherentFormalModule X I`.
- An index type `J`, open family `U : J → X.Opens`, and cover equation
  `hU : iSup U = ⊤`; no finiteness or nonemptiness is added.
- Formal systems `F G : CoherentFormalModule X I` and a morphism `α : F ⟶ G`.
  The dependency's `op n` component is level `n+1`, so `n : ℕ` covers exactly
  the node's positive levels.
- The local hypothesis is rendered as
  `∀ j n, IsIso ((Scheme.Modules.restrictFunctor (U j).ι).map
  (α.hom.app (op n)))`, precisely restriction of each component to each cover open.
- The conclusion is `IsIso α`, an explicit inverse `β : G ⟶ F` with both
  composition identities, and for every level an object-level isomorphism `e`
  whose hom and inverse are respectively `α.hom.app` and `β.hom.app`.
  These are exactly the node's componentwise isomorphism and inverse clauses.

No mismatch was found. In particular, the restriction functor is the recorded
`Scheme.Modules.restrictFunctor` from the dependency category, rather than tensor
pullback; the index universe `Type v` is independent because no limit over `J` is
taken; and the empty cover, empty scheme, zero ideal/system, zero objects, and all
positive levels (including level one represented by `op 0`) remain covered by the
signature. No characteristic or base-field assumption is introduced.

The source place was checked against Stacks Tag 087X (Lemma 30.23.2), including
the Noetherian scheme, quasi-coherent ideal, arbitrary open-cover locality, and the
componentwise inverse conclusion. Searches were independently repeated with the
item-scoped `msearch.py` LeanFinder query, repository and Mathlib `rg` searches for
`CoherentFormalModule`, `isIso.*restrict`, and the exact theorem name, and the
existing declaration search; they found only the dependency and generic single-
sheaf isomorphism lemmas, not this theorem. The module compiled cleanly with
`scompile.py`; no repair was necessary.
