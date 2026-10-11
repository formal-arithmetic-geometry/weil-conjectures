## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentFiltrationIntegralSubschemes` states
`AlgebraicGeometry.Scheme.Modules.exists_coherent_filtration_integral_subschemes`, with
` sorry` as its only proof. No definitions, extra nodes, dependency modules or statement
corrections are needed. The source was read at
https://stacks.math.columbia.edu/tag/01YF (Lemma 30.12.3). The local
`literature/stacks-project/coherent.tex` is absent on this machine; the official tag contains
both the statement and proof, and agrees with the node. No mathematical fault was found.

Clause-by-clause correspondence:

- A scheme X: `(X : Scheme.{u})`.
- Noetherian, explicitly locally Noetherian and quasi-compact:
  `[IsLocallyNoetherian X] [CompactSpace X]`. Mathlib's `IsNoetherian` has exactly these two
  parent classes; CompactSpace means quasi-compactness without any Hausdorff assumption.
- An O_X-module F: `(F : X.Modules)`.
- Coherent F: `(hF : RingedSpace.IsCoherent X.toRingedSpace F)`, using the dependency's
  recorded definition, including finite type and finite-type kernels on all opens.
- Integer m >= 0: `∃ (m : ℕ)`; this permits zero.
- A finite chain of sub-O_X-modules of F:
  `(c : Fin (m + 1) → Subobject F) (hc : Monotone c)`. Subobjects are isomorphism classes
  of monomorphisms into F, and their order is factorization of those monomorphisms, so this
  states genuine subsheaves of F. Their representatives are `(c k : X.Modules)`.
- The chain begins at zero and ends at F: `c 0 = ⊥ ∧ c (Fin.last m) = ⊤`.
  Bottom represents the zero subsheaf and top the whole sheaf, with no equality of chosen
  representatives required. These equations mean exactly equality of submodules.
- Every step is coherent: the explicit universal clause
  `∀ k : Fin (m + 1), RingedSpace.IsCoherent X.toRingedSpace (c k : X.Modules)`.
- For each j = 1,...,m: `∀ j : Fin m`. Here `j.castSucc` and `j.succ` index the two
  successive steps; thus the zero-based j corresponds to the node's one-based j+1.
- A closed immersion i_j : Z_j → X: `∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧ ...`.
- Integral Z_j: `IsIntegral Z`, the dependency's Mathlib class (nonempty, with domain
  sections on nonempty opens).
- An ideal subsheaf I_j of O_Z: an existential subobject
  `I : Subobject (C := Z.Modules) (SheafOfModules.unit Z.ringCatSheaf)`.
  `SheafOfModules.unit` is the structure ring sheaf viewed as its rank-one module; its
  O_Z-submodules are precisely ideal subsheaves. This uses existing subobjects and the
  existing structure module, and does not define a second notion of ideal sheaf.
- Nonzero I_j: `¬ IsZero (I : Z.Modules)`. This is categorical nonzeroness of the
  underlying sheaf, not nonzeroness of its global sections or properness of the ideal.
- Coherent I_j: `RingedSpace.IsCoherent Z.toRingedSpace (I : Z.Modules)`.
- The quotient is the cokernel of the inclusion: `cokernel (Subobject.ofLE
  (c j.castSucc) (c j.succ) (hc j.castSucc_le_succ))`. `ofLE` is the canonical monic
  factorization between the subobjects and commutes with their arrows into F.
- An O_X-linear isomorphism with the pushforward ideal: `Nonempty (... ≅
  (pushforward i).obj (I : Z.Modules))`. This is an isomorphism in X.Modules, with
  Mathlib's sectionwise scheme-module pushforward, not just an abstract group isomorphism.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`
  (locally affine locally ringed spaces and morphisms of locally ringed spaces).
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`;
  quasi-compactness from the scheme-conventions node is `CompactSpace X`.
- `Sheaf.AlgebraicGeometry.Coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules`, `SheafOfModules.Hom`
  and `SheafOfModules.unit`, as carried by `Scheme.Modules`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (closed embedding and surjective stalk maps).
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `def-pc-module-pullback` records
  `Sheaf.AlgebraicGeometry.TensorPullback`, `Scheme.Modules.tensorPullback`; its adjunction
  statement explicitly uses `Scheme.Modules.pushforward`. This item uses only that
  pushforward half, read in `Mathlib.AlgebraicGeometry.Modules.Sheaf`, so it imports no
  unused tensor-pullback module. The pushforward is exactly
  `SheafOfModules.pushforward i.toRingCatSheafHom`, with sections on i⁻¹(U).
- `Mathlib.CategoryTheory.Subobject.Basic`: `Subobject.ofLE`; `Subobject.Limits` supplies
  the bottom/top subobjects used for the endpoints. Cokernels are the existing categorical
  cokernels in the existing Abelian category X.Modules.

Edge cases checked before writing:

- F = 0 permits m = 0: Fin 1 has one step, bottom equals top for a zero object, and
  Fin 0 has no quotient conditions. No nonzero ideal or integral scheme is demanded.
- The empty scheme is allowed by both hypothesis classes. Its module category is trivial,
  so the same length-zero case applies.
- The unit ideal is allowed: the node asks for nonzero ideals, not proper ones.
- Integrality already requires nonempty Z, as in the node. No ambient nonemptiness,
  field, characteristic, separatedness, reducedness or irreducibility is imposed on X.
- u is explicit and arbitrary. Closed subschemes and their module sheaves lie in X's
  universe; there is no independent smaller universe restricting the closed subschemes.

Searches for an existing statement (msearch.py, group F1 and this item):

- LeanFinder query: `coherent module on a Noetherian scheme has finite filtration with
  quotients pushforwards of nonzero coherent ideals on integral closed subschemes`.
  Eight hits: the ring-level prime-quotient filtration/induction in
  `IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime` and
  `IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime`, and Noetherian scheme
  criteria; no scheme-level coherent filtration.
- Loogle query: `"filtration", "Coherent"`: zero hits.
- LeanSearch query: `coherent sheaf finite filtration integral closed subscheme ideal`:
  service unavailable (Internal Server Error); recorded as unavailable, no verdict.
- Mathlib grep query: `filtration|devissage`, subdirectory AlgebraicGeometry: zero hits.
- Source and project rg query: `filtration|coherent.*filter|` followed by the item id,
  over `WeilConjectures` and `lean/Sheaf`: hits are general categorical filtrations,
  representation filtrations, weight filtrations and spectral-sequence filtrations;
  none states this coherent sheaf lemma. The item-id search has no hit in the source.
- The proposed declaration and module names were checked by rg in
  `dag/lean_names_upstream.json`, the source and `lean/Sheaf`: no collision.
- Read the existing Subobject, ofLE, structure-module unit, and module-pushforward
  signatures and docstrings directly; these existing notions suffice without a new node.

Validation: server `scompile.py` succeeds with no errors or warnings. The initial compile
identified an ambient-category inference mismatch for the ideal subobject; specifying
`C := Z.Modules` fixes it without changing the statement. The delivered theorem's proof
is `by sorry`; there are no other declarations or proofs in the module. The docstring
carries the eight-step proof route from the node, including all non-elementary inputs.

## Second reading by F1

I independently opened the sandbox node and theorem, all eight statement-dependency
nodes, and the corresponding declaration sources. The local Stacks tree is absent;
I read the official Tag 01YF and fetched the official Stacks `coherent.tex` into the
sandbox as `coherent-source.tex`. Its section preamble (lines 2923–2941) assumes only
that X is Noetherian; the lemma at lines 3050–3067 has exactly the node's statement.
The proof at lines 3069–3141 explicitly includes the zero sheaf with m = 0.
Sources: https://stacks.math.columbia.edu/tag/01YF and
https://raw.githubusercontent.com/stacks/stacks-project/master/coherent.tex.

The object/hypothesis/conclusion list, matched independently against the Lean:

1. A scheme X: `(X : Scheme.{u})`. PASS. `Scheme` in Mathlib extends a locally
   ringed space with local affine charts; `Scheme.Hom` is a locally ringed-space
   morphism. This is the recorded def-pc-scheme, not an affine specialization.
2. X Noetherian: `[IsLocallyNoetherian X] [CompactSpace X]`. PASS. I read
   Noetherian.lean:57 and :280: these are precisely the two parent predicates of
   `IsNoetherian`. Local Noetherianity is checked on affine opens, equivalent to
   the dependency node's affine-cover formulation. CompactSpace asserts topological
   quasi-compactness and introduces no Hausdorff requirement.
3. An O_X-module F: `(F : X.Modules)`. PASS. Modules/Sheaf.lean:38 identifies
   `Modules` with `SheafOfModules.{u} X.ringCatSheaf`; its morphisms are linear
   presheaf morphisms. I read SheafOfModules and Hom in ModuleCat/Sheaf.lean:33–47.
4. F coherent: `(hF : RingedSpace.IsCoherent X.toRingedSpace F)`. PASS. I read
   Coherent.lean in full: finite type and finite-type kernels for every map from
   each finite free module on every open, exactly pqf-def-coherent. The same module
   carrier is used; no quasi-coherence assumption is substituted or added.
5. A length m >= 0: `∃ (m : ℕ)`. PASS. All nonnegative integral lengths are covered.
6. Coherent submodules F_0,...,F_m of F, increasing: `c : Fin (m + 1) → Subobject F`,
   `hc : Monotone c`, and the universal coherence clause on `(c k : X.Modules)`.
   PASS. A subobject is a monomorphism into the same F, modulo isomorphism over F.
   I read Subobject.Basic's `ofLE` and `ofLE_arrow`: the order gives monic
   inclusions commuting with the maps into F. These are actual subsheaves up to
   the usual categorical identification, not unrelated coherent objects.
7. Endpoints 0 and F: `c 0 = ⊥ ∧ c (Fin.last m) = ⊤`. PASS. I checked
   Subobject.Lattice: top is represented by the identity of F; bottom by the
   initial-object inclusion, hence the zero subsheaf in this abelian category.
8. Each j = 1,...,m: `∀ j : Fin m`, pairing `j.castSucc` with `j.succ`. PASS.
   Lean's index j corresponds to the node's j + 1. This quantifier follows the
   existential chain, so one chain works for all successive quotients.
9. An integral closed subscheme Z_j: `∃ (Z : Scheme.{u}) (i : Z ⟶ X),
   IsClosedImmersion i ∧ IsIntegral Z ∧ ...`. PASS. I read ClosedImmersion.lean:45
   (closed embedding, surjective stalk maps) and Properties.lean:240 (nonempty,
   domain sections on nonempty opens), with no additional hypotheses on X or i.
   This uses the dependency definitions, not a reduced or affine surrogate.
10. A sheaf of ideals in O_Z: `I : Subobject (C := Z.Modules)
    (SheafOfModules.unit Z.ringCatSheaf)`. PASS. I read the existing `unit` at
    ModuleCat/Sheaf.lean:173: it is the structure ring sheaf as its rank-one
    module. Sub-O_Z-modules of this module are precisely ideal subsheaves;
    the ambient category is explicitly Z.Modules, not X.Modules.
11. I nonzero and coherent: `¬ IsZero (I : Z.Modules)` and
    `RingedSpace.IsCoherent Z.toRingedSpace (I : Z.Modules)`. PASS. Nonzero refers
    to the sheaf itself, not to its global sections or to being a proper ideal.
12. Quotient by the adjacent inclusion: `cokernel (Subobject.ofLE
    (c j.castSucc) (c j.succ) (hc j.castSucc_le_succ))`. PASS. The ambient
    category is X.Modules, whose existing Abelian and HasColimits instances I
    read in Modules/Sheaf.lean. It is the categorical sheaf cokernel, not the
    unsheafified sectionwise quotient.
13. O_X-linear quotient/pushforward isomorphism: `Nonempty (... ≅
    (pushforward i).obj (I : Z.Modules))`. PASS. I read `pushforward` and
    `pushforward_obj_obj` in Modules/Sheaf.lean:166–171 and the recorded
    tensor-pullback dependency's adjunction at TensorPullback.lean:102. Both use
    the same sectionwise module pushforward, with sections on inverse-image
    opens and restricted scalars. No unused tensor-pullback import is needed.

Edge cases: PASS. For m = 0, Fin 1 has one chain element and Fin 0 has no
quotient conditions; bottom = top is possible exactly for zero F. Thus zero F,
the empty scheme, and the empty quotient index set are included. Integral Z
must be nonempty as the source requires, but X need not be nonempty. Unit ideals
are allowed; no properness constraint appears. No field, characteristic,
separatedness, ambient reducedness, or ambient integrality is assumed. The
explicit arbitrary universe u covers schemes and their same-universe sheaves;
closed subschemes can be represented in that universe. There are no unbound
variables or independently smaller test-object universes.

Independent H4 searches (using different wording from the worker):

- LeanFinder: `Noetherian scheme coherent sheaf devissage ideal sheaves integral
  closed subschemes`. Eight hits, all Noetherian scheme predicates/criteria;
  none is the required filtration theorem.
- Loogle: `"Coherent", "Subobject"`. Zero hits.
- LeanSearch: `finite chain coherent subsheaves quotients nonzero ideal sheaves
  integral subschemes`. Service unavailable, Internal Server Error; no verdict
  is inferred from the unavailable search.
- Direct rg over the pinned Mathlib, WeilConjectures, and project lean/Sheaf:
  `devissage|dévis|coherent.{0,50}filtr|filtr.{0,50}coherent|` followed by the
  proposed theorem name. No matching coherent-scheme filtration declaration.
  Other hits concern categorical prime-factor, coefficient, weight, or curve
  devissage. Existing module-sheaf, structure-module, subobject and pushforward
  declarations supply every notion needed here, without a new definition.

H5–H9: PASS. There is one named theorem with `by sorry` and no definitions or
proved auxiliary statements. Module and declaration docstrings identify Tag
01YF and the blueprint node. I checked the theorem's eight proof steps against
all eight DAG proof steps and the source: coherence/support preliminaries;
zero/isomorphisms/extensions; minimal support; reducible support; reduced induced
structure; annihilating ideal-power filtration; generic-point ideal inclusion;
partial-sum image filtration and the smaller-support cokernel contradiction.
The docstring retains the named non-elementary inputs. Imports supply the
coherence predicate, Noetherian hypotheses, closed immersion, and subobjects.

There are no new nodes, dependency modules, or statement corrections in this
delivery. No mismatch was found, so the Lean and node record are unchanged;
only this independent second-reading report was appended. The recorded
lean.statement is verbatim the theorem signature, excluding `:= by sorry`.

## Reviewer fix (R-cfi1207)

- Noetherian: `[IsLocallyNoetherian X] [CompactSpace X]` replaced by `[IsNoetherian X]` (STATE line NOETHERIAN SCHEME, M1 74f845ccf).
- Ideal sheaf of `𝒪_Z`: the ad-hoc `Subobject (SheafOfModules.unit Z.ringCatSheaf)` replaced by the project's one notion `I : Z.IdealSheafData` (M1 38987164c), with its module `I.toModules` (WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module, as in the landed ConductorIdeal modules); nonzero is `I ≠ ⊥`, coherence and the pushforward are on `I.toModules`. A coherent ideal on the Noetherian `Z` is quasi-coherent, so nothing is lost.
