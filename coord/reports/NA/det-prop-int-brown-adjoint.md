## Worker report

Item: `det-prop-int-brown-adjoint`. Module:
`Sheaf.SixFunctors.IntegralBrownAdjoint`. The theorem is
`AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.exists_integralBrownAdjoint`.
Its sole proof is `sorry`. Three auxiliary declarations belong to this same node:
`lowerShriek` is the actual full-subcategory lift of the recorded compactification
functor, `lowerShriekCommShift` inherits its ambient shift comparison, and
`brownAdjointAssertions` packages the complete conclusion. Their data are written
out; none selects a right adjoint from a bare existence assertion.

Source read: `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-int-brown/sk-prop-int-brown-adjoint.md`, its `.proof.md`, and the unit's
`sk-prop-int-brown.proof.md`. The DAG's expanded five-step proof is in the theorem
docstring. The source proof qualifies uniqueness by compatibility with counits,
as does the already corrected DAG statement.

Hypothesis-by-hypothesis rendering:

- A prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`.
- A field of positive characteristic different from ell: `(k : Type u) [Field k]`,
  `[Fact (ringChar k).Prime]`, `[Fact (ringChar k ≠ ℓ)]`. A field has either zero
  or prime characteristic; requiring prime ringChar is exactly positive characteristic.
- The finite extension E/Q_ell and its topological valuation ring:
  `(E : PadicAlgCl.FiniteIntermediateField ℓ)` and the existing condensed ring object
  `Profinite.padicIntegersRingObj ℓ E.val`. This is the finite-subextension encoding
  used by the dependencies, with the induced ell-adic topology; it is not the
  discrete ring or its constant sheaf.
- Schemes X,Y over k: explicitly bound `{X Y : Scheme.{u}}` and the two
  `[X.Over (Spec (.of k))]`, `[Y.Over (Spec (.of k))]` instances. For each structure
  morphism, `[LocallyOfFiniteType ...] [QuasiCompact ...]` is finite type, and
  `[IsSeparated ...]` is separatedness.
- A separated finite-type k-morphism: `(f : X ⟶ Y)`, `[f.IsOver (Spec (.of k))]`,
  `[LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]`.
- The chosen compactification: `(c : Compactification.BoundaryCompactification f)`.
  Its underlying `c.obj.obj` has proper second leg and open first leg; `c.obj.property`
  gives quasi-compactness of the open immersion. Quantification over this datum lets
  the consumer use its already chosen compactification, without making another choice.

Clause-by-clause rendering:

- Module-object pro-etale categories, the precise Dbc and ordinary localizing closure:
  the existing `IntegralCompactSupport.Ambient`, `generators`, and `localizing`.
  These use `constantModelBoundedConstructible`, not the broader upstream predicate.
  No derived completeness or completed direct sums are introduced.
- The left adjoint on Loc(Dbc): `lowerShriek Λ c.obj.obj h`. Its definition lifts
  `(localizing Λ X).ι ⋙ image Λ c.obj.obj` to the full codomain. Here `image` is
  the already recorded `rightDerivedLowerShriekOfCompactification`, literally
  exact levelwise extension by zero followed by right-derived pushforward.
  The existential `h` provides only preservation of membership, not arbitrary
  functor data; maps are the original ambient maps.
- Triangulated categories: existential `hX`, `hY` prove that the actual closure
  properties are triangulated. The explicit instance-argument lambdas use these
  proofs to give the inherited full-subcategory triangles; they impose no new
  hypothesis on X or Y and choose no unrelated triangulated structure.
- Existence of the right adjoint in the displayed direction: `∃ G : Loc_Y ⥤ Loc_X`.
- Exactness: `∃ s : G.CommShift ℤ` and, with that instance explicitly installed,
  `G.IsTriangulated`. No exactness axiom is replaced by mere existence of an adjoint.
- Natural Hom bijections for every M,N: `∃ adj : lowerShriek ... ⊣ G` gives
  `adj.homEquiv M N` and both naturality laws, with no boundedness restriction on
  M or N beyond belonging to the displayed localizing closures.
- Unique natural isomorphism compatible with counits: for every J and adjJ,
  `∃! e : G ≅ J, ∀ N, F.map (e.hom.app N) ≫ adjJ.counit.app N = adj.counit.app N`.
  Thus uniqueness is normalized as required, rather than asserted for all natural
  isomorphisms regardless of adjunction.
- Identification with sk-prop-sf-existence under Dctf=Dbc: `_eX` and `eY` assert
  the actual equality of the Loc(Dctf) and Loc(Dbc) object properties. For every
  restricted general functor, any right adjoint J and its adjunction, the final
  clause gives a unique comparison between `G ⋙ Loc_X.ι` and
  `ObjectProperty.ιOfLE (le_of_eq eY.symm) ⋙ J ⋙ LocCtf_X.ι`. Both are functors
  into the same ambient derived category. The comparison is normalized by the
  equality of their ambient counits after applying the same `image` functor.
  This includes any witness of `exists_localizingExceptionalAdjoint`, and avoids
  introducing a noncanonical choice of its existential witness. Full inclusions
  reflect equality and isomorphisms, so this is the asserted identification of
  the right adjoints on the equal full subcategories. The equality for X ensures
  that their values have exactly the same domain of membership.

Dependency declarations read and used:

- `sk-def-sfb-dc-setting`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` and the
  scheme-setting binders. The theorem takes the fixed compactification explicitly;
  it does not invoke this choice again.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`,
  `HasFiniteConstantLocalModel`, `IsConstantModelConstructible`,
  `constantModelBoundedConstructible`, `ConstantModelConstructibleFiniteTor`
  in namespace `AlgebraicGeometry.ProEtale`; used through the recorded closures.
- `sk-def-localizing-closure`: `Sheaf.Paper.LocalizingAdmissibleCoefficients`
  and its imported `Sheaf.Paper.LocalizingClosure`; `CategoryTheory.localizingClosure`,
  `AlgebraicGeometry.ProEtale.localizingClosureProEtale`, and the admissible
  integral coefficient case. Reuse both existing closures with their recorded
  indexing convention, without introducing a second closure definition.
- `det-prop-int-brown-construction`:
  `Sheaf.SixFunctors.IntegralLocalizingCompactSupport`, namespace
  `AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport`, declarations
  `Ambient`, `image`, `generators`, `localizing`, `integralLocalizingCompactSupport`.
- `sk-def-sfb-module-derived-lower-shriek`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek`,
  `AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification`;
  used through `image`, including its actual action on morphisms.
- `det-def-localizing-closure-ctf-equals-bc`:
  `Sheaf.Paper.LocalizingClosureCtfEqualsBc`,
  `AlgebraicGeometry.ProEtale.localizingClosure_ctf_equals_bc` and
  `localizingClosureCtfEqualsBcAssertions`; imported for proof step 2.
- `sk-prop-sf-existence`: `Sheaf.Paper.LocalizingExceptionalAdjoint`,
  `AlgebraicGeometry.ProEtale.CondensedRing.localizingLowerShriek`,
  `exists_localizingExceptionalAdjoint`; the former occurs in the final comparison,
  the latter is the proof's existence input, not a new unbounded adjoint assumption.
- `def-weil-triangulated-category`: Mathlib
  `CategoryTheory.Pretriangulated`, `CategoryTheory.IsTriangulated`,
  `CategoryTheory.Functor.IsTriangulated` from `CategoryTheory.Triangulated.*`.
- `sk-def-nagata-sketch-data`: `Sheaf.Compactification.BoundaryRefinement`,
  `AlgebraicGeometry.Compactification.BoundaryCompactification` and
  `QuasiCompactObjects`.
- Proof leaves: Mathlib `Adjunction.rightAdjointUniq` and its counit equation
  (`CategoryTheory.Adjunction.Unique`); finite type, affine qcqs, separated implies
  quasi-separated, and qcqs permanence in the explicitly imported
  `AlgebraicGeometry.AffineScheme` and `AlgebraicGeometry.Morphisms.*` modules.
  Other recorded proof-dependency modules are already public statement imports.

Searches (2026-10-18):

- `msearch.py ... leansearch "An exact compactly supported direct image functor on
  the localizing closure of integral constructible complexes has an exact right
  adjoint"`: 8 hits, ordinary sheaf/module pushforward adjunctions and the abstract
  `CategoryTheory.Functor.rightAdjoint`; none is this geometric existence theorem.

- `msearch.py ... leanfinder "compactly supported direct image integral condensed
  coefficients localizing constructible category exact right adjoint"`: 8 hits,
  including `CondensedMod.LocallyConstant.adjunction` and
  `LightCondMod.LocallyConstant.adjunction`; none states this geometric adjoint.
- `msearch.py ... loogle "CategoryTheory.Adjunction.rightAdjointUniq,
  CategoryTheory.Functor.IsTriangulated"`: 0 hits. This does not negate the
  individual uniqueness and triangulated-functor APIs, which were read directly.
- `msearch.py ... grep "integral.*Adjoint|localizing.*Adjoint|Brown" CategoryTheory`:
  3 hits concerning authors named Browning/Merten, no matching statement.
- `rg -n 'integral.*[Aa]djoint|[Aa]djoint.*[Ii]ntegral|
  det-prop-int-brown-adjoint'` on upstream `WeilConjectures` and side `lean/Sheaf`:
  finite-coefficient inverse-limit adjoints and references to this pending node;
  the upstream integral coefficient theorem is on different etale inverse-system
  categories. The general localizing adjoint is an input, not this exact statement
  on Loc(Dbc) with an explicit comparison to Loc(Dctf).
- Direct name searches in Mathlib, upstream, and the side library for
  `brownAdjointAssertions`, `exists_integralBrownAdjoint`, and
  `IntegralCompactSupport.lowerShriek` found no collision. Searches for
  `def lowerShriek` found only declarations in other namespaces/categories.
- `scompile.py --source` read the currently available LocalizingClosure,
  LocalizingExceptionalAdjoint, and IntegralLocalizingCompactSupport sources to
  check the exact live interfaces in addition to reading the local source files.

Edge cases checked before writing: zero complexes and the empty scheme are
allowed; no Nonempty object hypothesis appears. The category includes all
localizing objects, without artificial boundedness on M,N. The general Hom and
comparison clauses cover every object and every other adjunction. Identity
morphisms and all choices of quasi-compact compactification are included. The
unramified/trivial finite extension is allowed, as are all ramified finite
extensions. Characteristic zero is intentionally excluded by the source's
positive-characteristic standing assumption. The ambient module-object site and
coefficient universes remain those of the recorded framework (`Scheme.{u}`,
`Ab.{u+1}`), with no imposed equality of site object and morphism universes.
Ordinary closure coproduct conventions are reused unchanged. The uniqueness
condition is essential: arbitrary automorphisms of a right adjoint need not be
unique without the counit equation.

No statement correction, disputed statement, new node, or dependency repair.
Only the item's `lean` field is changed. Compilation uses only `scompile.py`.
The final standalone sandbox and library-path checks both passed without warnings
(8.3 s and 7.8 s respectively); the only postponed proof is the named theorem.

## Second reading by NA

This is the writing worker's separate rereading, not an independent agent review;
the dispatcher brief assigns independent review to the maintainer and forbids
starting another agent. I reopened the node and the completed module. The binder
checks are the prime, positive unequal characteristic, finite extension, both
separated finite-type structure morphisms, separated finite-type k-morphism,
and fixed quasi-compact compactification listed above. The conclusion checks
are the precise Loc(Dbc), actual composite rather than a derived underived
composite, exact G with its shift comparison, natural Hom bijections, unique
counit-compatible comparison, and comparison to the general Loc(Dctf) adjoint.
No hypothesis or conclusion mismatch was found in this pass. Compilation flagged
three instance arguments used only implicitly; these were renamed `_triX`,
`_triY`, `_comm`, including their explicit applications, with unchanged types. In particular the
last clause is explicit, not merely asserted in a docstring, and no direct-sum
preservation conclusion for G beyond this node's statement was added. All
variable/universe binders are explicit and autoImplicit is disabled.
