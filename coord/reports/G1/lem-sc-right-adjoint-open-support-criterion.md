## Worker report

The module states `AlgebraicGeometry.rightAdjoint_open_support_criterion`, with one
`by sorry` and no new definitions. The node is unchanged except for its Lean record.

Hypotheses and objects:
- `X Y : Scheme.{u}` and `CompactSpace`/`QuasiSeparatedSpace` on each are exactly
  the two quasi-compact quasi-separated schemes. The morphism `f : X ⟶ Y` is arbitrary;
  no properness, flatness, or Noetherian hypothesis is imposed.
- `V : Y.Opens`, `hV : IsCompact (V : Set Y)` give the quasi-compact open, and
  `U : X.Opens`, `hU : U = f ⁻¹ᵁ V` give its full inverse image. The immersions
  called j and j_U in the node are `V.ι` and `U.ι`.
- `a` has domain `schemeDerivedQCohCategory Y` and codomain
  `schemeDerivedQCohCategory X`. `adj` identifies it as a right adjoint to the
  lift of the RECORDED `schemeDerivedDirectImage f`, through the full-subcategory
  inclusions. `hpush` is only the proof needed to form that lift, not an arbitrary
  functor or added geometric constraint: qcqs direct image preserves QCoh.
- Derived localization instances are supplied for X, Y, U, V, all at the same
  morphism universe w; u and w are explicitly bound. These specify the chosen
  localizations, not a restriction on the schemes.
- The repeated restriction expressions use the existing `SheafOfModules.overFunctor`
  followed by the existing `Scheme.Modules.overEquiv`; their exact derived functor
  is Mathlib's `Functor.mapDerivedCategory`. Additivity is supplied explicitly by
  `Functor.additive_of_preserves_binary_products`, because implicit synthesis did
  not find it for the composite. The exactness instances are inferred; none is
  redefined or postponed.
- `adjOpen` is the derived open adjunction between that concrete restriction on Y
  and `schemeDerivedDirectImage V.ι`. `hopen` supplies QCoh membership of
  `Rj_*j^*K`, required to apply the QCoh functor a to its unit. Both are the standard
  constructions for the specified open; neither encodes the desired conclusion.

Clauses:
1. First conjunct: invertibility for every K with `∃ n : ℤ, K.obj.IsGE n` is
   equivalent to vanishing on U of a(Q), for every Q with the same bounded-below
   condition whose restriction to V is zero. `IsGE` is the standard derived
   t-structure predicate, so the existential bound allows arbitrary lower bounds.
2. Second conjunct: the identical equivalence with both boundedness tests removed.
3. Third conjunct: `(∀ I : Type u, PreservesColimitsOfShape (Discrete I) a)`
   implies equivalence of bounded and unbounded invertibility conditions. Together
   with the first two conjuncts this is also equivalence of all four conditions
   under the direct-sum hypothesis. Preservation is NOT assumed in parts (1),(2).
   Every small indexing set, including the empty set, is allowed.

Canonical-map rendering: the source itself, immediately after equation (the project server),
identifies invertibility of its entire open-square map with invertibility of its
first arrow `a(K)|U → a(Rj_*j^*K)|U`. The latter is the actual map written here:
`adjOpen.unit.app K.obj`, lifted by `ObjectProperty.homMk`, mapped by a, forgotten
through the full-subcategory inclusion, and restricted to U. The other two arrows
are canonical isomorphisms; no arbitrary transformation is supplied. The right
adjoint a_V is consequently eliminated from the isomorphism TEST by the source's
canonical identification `a(Rj_*L)|U ≅ a_V(L)`. The docstring explains this
identification and contains all three proof steps with the proof-dependency ids.
This is the source's own equivalent formulation, with the same strength and same
objects K,Q,a; it does not assert existence of some invertible comparison map.

Support on a closed complement is written concretely as `IsZero` of derived open
restriction. Exact restriction commutes with cohomology and a sheaf is zero iff
all its stalks vanish, so this is precisely cohomology supported on the complement,
including for unbounded complexes. There is no unspecified support predicate.

Dependency declarations read and used:
- def-weil-pbc-scheme-conventions fixes no declaration; its record expressly asks
  citers to use the Mathlib scheme/property definitions. Here Scheme, Opens,
  CompactSpace and QuasiSeparatedSpace supply its applicable conventions.
- Sheaf.AlgebraicGeometry.DerivedCategory: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory` (read full definitions).
- Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage:
  `schemeDerivedDirectImage` (read full signature and ringed-space specialization).
  The imported module also exposes the moduleRings and exact open-restriction
  constructions of Sheaf.Paper.DerivedHomMayerVietoris.
- Mathlib: `ObjectProperty.lift`, `.ι`, `.homMk`; `Functor.mapDerivedCategory`;
  `Functor.additive_of_preserves_binary_products`; `Scheme.Modules.overEquiv`;
  `DerivedCategory.IsGE`; `IsZero`; `PreservesColimitsOfShape`.

Edge cases checked before the final statement: V empty makes both restriction
tests zero and both support assertions automatic; V = top makes the unit invertible
and supported objects zero. Empty schemes and zero complexes are allowed. Arbitrary
negative lower bounds are allowed, and the unbounded clauses have no truncation.
No bounded-below condition is imposed on a(Q). No finite-dimensionality or
characteristic assumption appears. Common localization universe w is an arbitrary
chosen universe large enough to carry all four localizations.

Searches:
- LeanFinder: "right adjoint derived quasi-coherent category restriction open support
  criterion": eight generic sheaf/open-immersion adjunction hits, no criterion.
- Loogle: "CategoryTheory.Adjunction, CategoryTheory.NatTrans": no hits.
- LeanSearch: "right adjoint restriction quasi compact open supported complexes":
  unavailable (Internal Server Error), recorded in searches.jsonl.
- msearch grep: "right.adjoint.*support|open.support.*criterion" in AlgebraicGeometry:
  no hits.
- rg in Mathlib AlgebraicGeometry, upstream WeilConjectures, and project lean/Sheaf
  for "adjoint.*support|support.*adjoint": upstream unrelated étale supported-class
  and pro-étale closed-immersion declarations; project sibling
  ProperFlatRightAdjointOpenSupport states the special support conclusion for
  proper flat finitely presented f, not this arbitrary-f criterion.
- rg for the node id in upstream: no hits. Searches for open-square constructions
  and derived restriction found the shared restriction constructions, reused here.

Source opened: https://stacks.math.columbia.edu/tag/0E4G, equation (the project server), its
following paragraph, Lemma 48.4.3 and its proof. The local Stacks checkout was absent.
No statement correction, new node, dependency replacement or disputed claim.

Validation: server single-file compile and deliver2.py --no-push (see final result).
Independent second reading is left to the designated second worker.


## Second reading by G1

I independently opened the item's complete node and delivered Lean module,
all three statement-dependency nodes and their recorded declarations. I read
Stacks `duality.tex`, section `section-restriction-to-opens`, equation
`equation-sheafy` and lemma `lemma-when-sheafy` with its proof. The local
Stacks checkout is absent; I read the upstream raw TeX at
https://raw.githubusercontent.com/stacks/stacks-project/master/duality.tex
and checked its numbered presentation at https://stacks.math.columbia.edu/tag/0E4G.
The source's standing assumption is qcqs schemes, with no field, characteristic,
Noetherian, properness or flatness hypothesis on f.

Object, hypothesis and conclusion inventory, matched to the actual signature:

1. Schemes X and Y, each quasi-compact and quasi-separated:
   `{X Y : Scheme.{u}}`, `[CompactSpace X]`, `[QuasiSeparatedSpace X]`,
   `[CompactSpace Y]`, `[QuasiSeparatedSpace Y]`. Verdict: exact; compact here
   means quasi-compact and does not add a Hausdorff assumption.
2. An arbitrary morphism f from X to Y: `(f : X ⟶ Y)`. Verdict: exact,
   with no extra geometric condition on f.
3. Quasi-compact open V in Y: `(V : Y.Opens)` and
   `(hV : IsCompact (V : Set Y))`. Verdict: exact.
4. Its full inverse-image open U in X: `(U : X.Opens)` and
   `(hU : U = f ⁻¹ᵁ V)`. Verdict: exact; U is not an arbitrary smaller open.
   The node's j and j_U are the inclusions `V.ι` and `U.ι`.
5. The quasi-coherent derived categories and derived pushforward:
   `schemeDerivedQCohCategory X/Y` and `schemeDerivedDirectImage f`.
   Verdict: the recorded dependency definitions are used. In DerivedCategory.lean
   I checked that QCoh means `∀ n : ℤ, IsQuasicoherent (H^n K)` in the full
   subcategory of the shared module-sheaf derived category. In
   SchemeDerivedDirectImage.lean I checked that pushforward specializes
   `RingedSpace.derivedModuleDirectImage`; I also opened its K-injective/right
   derived functor construction in RingedSpaceDerivedDirectImage.lean.
   The conventions dependency explicitly fixes no new declaration.
6. Right adjoint a to that Rf_*: the functor binder `a` and `adj`, whose
   left functor is `ObjectProperty.lift` of the recorded pushforward composed
   with the QCoh inclusion. Verdict: exact direction and objects. I read
   `ObjectProperty.lift`, `homMk` and the inclusion signatures: these only
   restrict a functor/morphism to the full subcategory, without altering it.
   `hpush` supplies membership for this lift; it is the standard qcqs
   quasi-coherence theorem, rather than a new constraint on f or a.
7. Open restriction and the canonical comparison to a_V: every displayed
   restriction is the derived exact functor of `SheafOfModules.overFunctor`
   followed by `Scheme.Modules.overEquiv`, with explicit categories on the
   equivalence. I read `overEquiv`, `Functor.mapDerivedCategory` and the shared
   exactness instances in DerivedHomMayerVietoris.lean. Verdict: the existing
   notion of restriction, no private replacement.
   The node's a_V and its comparison are eliminated only from the isomorphism
   test, exactly as the paragraph following equation (the project server) does: the
   comparison is the restricted unit followed by two canonical isomorphisms.
   The Lean tests precisely the restricted image under a of
   `ObjectProperty.homMk (adjOpen.unit.app K.obj)`. Its target membership is
   `hopen K`, a consequence of QCoh restriction and qcqs open pushforward.
   The binder `adjOpen` supplies an adjunction for those fixed functors; it
   cannot choose an arbitrary map. Changing an adjunction structure changes
   its unit by an invertible natural automorphism of the right functor, so
   this isomorphism test agrees with the standard unit for every such choice.
8. Bounded-below equivalence, for every K and every supported Q in D_QCoh^+(Y):
   the first conjunct uses `∀ K` with `(∃ n : ℤ, K.obj.IsGE n)` and `IsIso`
   of the restricted unit image, iff `∀ Q` with the same existential lower
   bound and `IsZero` of restriction to V implies `IsZero` of restriction
   of `a.obj Q` to U. Verdict: both directions, all objects, same support.
   I checked `DerivedCategory.isGE_iff`: this is vanishing of cohomology
   in every degree below n. The output a(Q) is not assumed bounded below.
9. The same equivalence without boundedness: the second conjunct repeats
   the map and support tests with no `IsGE` antecedents. Verdict: exact
   unbounded assertion; support is cohomological support, because exact
   restriction commutes with cohomology and vanishing is stalkwise.
10. Direct sums upgrade the bounded assertion to the unbounded assertion:
    third conjunct has `(∀ I : Type u, PreservesColimitsOfShape (Discrete I) a)`
    as antecedent and the bounded/unbounded map conditions as an iff.
    Verdict: exact. The reverse implication is restriction of quantification;
    combined with the first two conjuncts it yields equivalence of all four
    conditions under the direct-sum hypothesis. No direct-sum preservation
    is assumed for either of the first two equivalences.

Edge cases: empty V gives empty U and zero restrictions; top V gives U = top
and the identity-open unit is invertible. Empty X or Y and zero complexes
are not excluded. The integer lower bound can be negative or zero, and the
unbounded clauses contain no implicit bound. There is no characteristic or
coefficient-field restriction. `I : Type u` covers all small set-indexed sums
in the universe of module values, including the empty index set. Both u and w
are explicitly declared. The four `HasDerivedCategory.{w}` binders are choices
of localizations in a common sufficiently large morphism universe, not
finite-dimensionality, smallness of schemes, or extra geometric assumptions.

Independent searches (also recorded in searches.jsonl):

- LeanFinder, "derived pushforward right adjoint localization closed complement
  vanishing": eight generic derived-adjunction/localization hits, no criterion.
- Loogle, `CategoryTheory.Adjunction, CategoryTheory.Limits.IsZero`: two abelian
  Serre/Bousfield localization lemmas, neither this derived scheme statement.
- LeanSearch, "derived category right adjoint preserves support if and only if
  commutes with open restriction": unavailable, Internal Server Error.
- `rg` on project Lean, upstream WeilConjectures, and Mathlib AlgebraicGeometry
  with `adjoint.*(support|complement)|support.*adjoint`, and separately
  `rightAdjoint.*(open|restrict)|open.*rightAdjoint|adjoint.*locali[sz]`:
  only unrelated etale/pro-etale support material and the project's proper-flat
  specialization. I opened ProperFlatRightAdjointOpenSupport.lean; it assumes
  proper, flat, locally finitely presented f and states support preservation,
  so it does not replace the arbitrary-f equivalences reviewed here.
- Searched `dag/lean_names_upstream.json` for this node id and declaration:
  no entry. Existing derived restriction and derived categories are reused.

No new definition node, dependency replacement or statement correction is
present or needed. No mismatch was found, and no Lean or node text was changed.
The declaration docstring explains the source's equivalent map test and all
three proof steps with their dependency ids. There are no definitions with
postponed data, no proved theorem, no file-local notation/instance, and precisely
one theorem with proof `by sorry`. All variables and universes are bound, lines
fit 100 columns, and the recorded signature matches the declaration after the
contract's whitespace normalization.

Validation: independent server single-file compilation passed with exit code 0,
no errors or warnings, in 12.5 seconds. Delivery dry run and final push follow.
