## Worker report

The delivery states `AlgebraicGeometry.ProEtale.finiteExceptionalDomain` in
`Sheaf.SixFunctors.FiniteExceptionalDomain`. Its proof is exactly `sorry`. Four public
helpers in the same owning module express the node's restriction: `left`, `right`,
`Restriction`, and `Conclusion`. These are not new notions requiring new DAG nodes:
`left` and `right` are the canonical `ObjectProperty.lift` restrictions, `Restriction`
is a record of precisely the asserted conclusions and their normalizations, and
`Conclusion` specializes this record to the actual positive finite coefficient quotient.
Their data contain no sorry, no arbitrary functor, and no choice from mere existence.
No statement or dependency node was changed, and there are no new nodes or dependency repairs.

Hypotheses and clauses, checked against the complete node text:

- The fixed algebraic closure of the finite field of characteristic p is
  `D : WeilConjectures.FiniteFieldDatum.{u}`. Its `k₀`, `k`, finite-base and
  algebraic-closure fields are the recorded global datum, not just an arbitrary
  separably closed field. The prime and exclusion are `(l : ℕ) [Fact l.Prime]`
  and `(_hl : l ≠ D.p)`.
- E/Q_l is `(E : Type u) [Field E] [Algebra (Padic l) E]`
  `[FiniteDimensional (Padic l) E]`. The valuation ring and uniformizer are the
  actual recorded coefficient-extension integers and chosen uniformizer, used by
  `Padic.coefficientExtensionRing l E n`. `(n : ℕ) (hn : 1 ≤ n)` excludes the
  zero level exactly as the node does. `Conclusion` installs the existing
  `Padic.finite_coefficientExtensionRing l E n hn`, not a new finiteness premise.
  `ULift.{u + 1}` is the standard coefficient size lift for the actual small sites.
- X and Y are `Scheme.{u}`, with `Over (Spec (.of D.k))` instances. For each
  structure map, `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` express
  separated finite type over k. The binder f has `f.IsOver (Spec (.of D.k))`,
  `IsSeparated f`, `LocallyOfFiniteType f`, and `QuasiCompact f`.
- The supplied `c : Compactification f` retains X, its open immersion `c.i`,
  proper part `c.g`, and factorization equation. `[QuasiCompact c.i]` is exactly
  the node's quasi-compact open condition. The dimension bound is `(d : ℕ)` and
  `(_hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞))`, with the correct bottom
  value for an empty compactifying scheme. There is no extra HasCompactification,
  bounded-below-adjoint, ambient-adjoint, invertible-exponent, or preservation hypothesis.
- C_T,n is the existing `ProEtale.DerivedCategoryFiniteTor (ModuleCat Λ) T`.
  Its object predicate is the recorded
  `ProEtale.DerivedCategory.constructibleFiniteTor (ModuleCat Λ) T`: bounded
  constructible and finite Tor amplitude, tested against all degree-zero module
  sheaves. At these finite quotients the existing constructible-origin comparison
  identifies the etale-origin reading with the intrinsic constructible-cohomology
  reading. This is the native fixed-module declaration expressly included in the
  current `def-weil-finite-tor-amplitude.lean.declarations`; it is not a new predicate.
- F_c,n is the existing `rightDerivedLowerShriekOfCompactification (ModuleCat Λ) c`,
  which is exactly extension by zero followed by proper derived direct image.
  `left` lifts this functor to the full finite-Tor subcategories. Its morphisms are
  the same ambient maps, wrapped by `ObjectProperty.lift`.
- The node says to let f_c,n^times be the ordinary etale right adjoint at c.
  `Conclusion` quantifies over that G and its adjunction
  `Etale.rightDerivedLowerShriekOfCompactification (ModuleCat Λ) c ⊣ G`.
  Such an adjoint exists by the recorded ordinary-etale Brown theorem; this is
  quantification over a choice the statement explicitly makes, not an extra
  pro-etale adjoint assumption. It avoids replacing c by the opaque compactification
  extracted from a Prop-valued HasCompactification instance.
- G_c,n is literally `(comparisonLowerStar (ModuleCat Λ) Y).rightDerivedFunctor ⋙ G ⋙
  (comparisonUpperStar (ModuleCat Λ) X).mapDerivedCategory`, namely Rnu_Y,*,
  the specified etale right adjoint, then nu_X^*. `right` is its full-subcategory lift.
- Both preservation assertions are `Restriction.preservesLeft` and `preservesRight`.
  They are fields of the *output* record; its existence is asserted by the theorem.
- The natural class-relative bijections are the existing
  `ComparisonClassAdjunction.homEquiv`, with its two naturality laws and normalized
  compact-support/comparison/ordinary-adjunction chain. `Restriction.classData` retains
  this original datum. `Restriction.adjunction` gives the adjunction on precisely
  the full finite-Tor categories, including both triangle identities.
  `Restriction.homEquiv` identifies its Hom equivalence, arrow for arrow under the
  full inclusions, with those class-relative bijections.
- `Restriction.unit` and `counit` identify the included components with the image
  of the identity under the class bijection and its inverse, respectively. These
  are exactly the node's class-relative unit and counit, not unspecified units.
- `Restriction.comparison` ranges over every other compactification, with
  `comparison_hom` requiring that each component is the original
  `classData.comparison`. `comparison_homEquiv` is the precise Hom-preservation
  equation, and `comparison_id` and `comparison_cocycle` are the original laws
  read in the finite-Tor categories. The recorded `ComparisonClassAdjunction`
  normalizes all right functors to the single chosen etale adjoint; the right
  comparison is consequently the identity, as its source module explicitly states.
  Hence the two-functor comparison cocycle is retained, with a trivial right factor.
- The adjunction is on Dctf only. The auxiliary class datum asserts only the known
  bounded-below etale-origin Hom bijections. No arbitrary unbounded pro-etale
  adjunction is asserted.

Dependency declarations and source reading:

- `WeilConjectures.Compactification.RefinementCategory`:
  `AlgebraicGeometry.Compactification.Refinement`, `category`; the compactification
  type itself is the existing proper/open factorization. Read their complete
  signatures, fields, properness explanation and category construction.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, defined as
  `Order.krullDim (IrreducibleCloseds T)` with codomain `WithBot ℕ∞`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible`, and its recorded native fixed-module
  interface `ProEtale.DerivedCategory.boundedConstructibleIntrinsic`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`:
  `WeilConjectures.finiteTorConstructibleEtale`, `finiteTorConstructible`,
  `finiteTorConstructibleCategory` and the recorded native
  `ProEtale.DerivedCategory.constructibleFiniteTor`. Read the full definitions and
  the upstream TorAmplitude module, including `DerivedCategoryFiniteTor` and its
  inclusion. No second Tor or constructibility definition is supplied.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison`, finite-limit preservation, and
  `proEtaleSiteComparisonModules`; the fixed-module comparison functors used above
  are precisely the endpoints of that recorded module adjunction.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`:
  `Scheme.sfIntrinsicCompactSupport`, the exact intrinsic formula
  `D(sfIntrinsicExtensionByZero c.i A) ⋙ proEtaleConstantDerivedDirectImage c.g A`.
  Our ambient left functor uses its original fixed-module presentation, with
  exactly the same j and p. The canonical finite-coefficient exact tensor realization
  identifies these presentations; we do not define compact support again.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`:
  `ConstructibleExceptionalCoefficients.System`, its `RingSystem.finiteRight`, and
  the recorded `ProEtale.sfFiniteExceptionalAt`. Read the latter's full formula and
  docstring. The output here uses the same comparison composite with a specified
  ordinary etale adjunction, retaining the node's chosen c explicitly.
- The proof imports include the exact recorded modules of `lem-trf-open-ctf`,
  `cor-sf-direct-image-ctf-proetale`, `thm-sf-preservation-class`,
  `lem-sf-proetale-constructible-origin`, `thm-sf-ambient-adjoint-class`, and
  `lem-kun-dimension-finite-type`, together with the Mathlib proper/finite-type
  and `Adjunction.mkOfHomEquiv` leaves. The recorded class module
  `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom` publicly reexports
  `ComparisonClassAdjunction`; the statement uses that precise normalized record.

The current blueprint source was opened under `literature/blueprint/latest/`,
`sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md`. It cites the
exceptional adjunction, constructible preservation, compactification coherence, and
coefficient comparisons. The item's five accepted proof steps are reproduced in the
main theorem docstring, including the dimension-bound argument at another compactification.

Searches (the wrapper also records these in searches.jsonl):

- LeanFinder, “A class relative exceptional adjunction restricts to bounded
  constructible finite Tor complexes preserving its unit counit and compactification
  cocycle”: eight derived-adjunction lemmas; none states the geometric preservation
  plus the node's restricted normalized adjunction.
- Loogle, `CategoryTheory.Adjunction.restrictFullyFaithful`: six exact abstract
  restriction and unit/counit lemmas. None establishes this pair's preservation.
- Mathlib grep, `Adjunction.*restrict|restrictFullyFaithful`,
  `CategoryTheory/Adjunction`: five hits in Adjunction/Restrict.lean. Abstract tool only.
- LeanSearch, “The exceptional adjunction for compact support on finite Tor
  constructible pro etale complexes is the restriction of the etale origin class
  adjunction with its units counits and compactification cocycle”: eight unrelated
  condensed/constant-sheaf/localization/core-adjunction hits, no exact statement.
- Project and upstream rg searches for `lem-sf-package-finite-exceptional-domain`,
  `finiteExceptional`, `DerivedCategoryFiniteTor`, `constructibleFiniteTor`,
  `rightDerivedUpperShriekOfAdjunction`, and `boundedConstructibleIntrinsic`:
  the reusable definitions and partial assertions described above exist.
  `UpperShriekFiniteness.DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction`
  uses the compactification extracted by HasCompactification, rather than the
  supplied c and its normalized Hom class. It does not state this entire node.
  No declaration tagged with this item's id existed. The newer recorded
  `SpecifiedExceptionalClassHom` avoids exactly this compactification-choice issue.

Edge cases checked before the final statement:

- n=0 is excluded, n=1 is included, and there is no flatness assumption on A_n.
- Empty X, Y, or compactifying scheme are included: no Nonempty hypothesis, no
  dimension converted to an invalid nonnegative integer, no maximum of an empty
  family. d=0 is allowed, and bottom dimension satisfies the displayed bound.
- Zero complexes and all morphisms of the full subcategories are included.
- Arbitrary finite-Tor intervals are allowed; no additional cohomological bound or
  prescribed interval is imposed on K and L.
- Every compactification is included in the comparison fields, and the identity,
  repeated-object and three-object cocycle cases are explicit.
- The conclusion quantifies over every ordinary-etale adjoint equipped with its
  adjunction, so it retains the arbitrary-choice case via uniqueness respecting
  its unit and counit. It neither assumes nor chooses a pro-etale ambient adjoint.
- `autoImplicit false` and the declared universe u prevent auto-bound variables.
  The coefficient lift is u+1 while schemes remain u; site universes are not equated.

No STATEMENT-DISPUTED flag or source-based correction is needed.

## Second reading by Q103

I reopened the node and reread the completed module after compilation. This was a
separate self-review pass; the dispatcher explicitly forbids spawning another agent,
and the maintainer will perform the independent review.

The initial draft had three real mismatches, all removed: it generalized the base
and coefficients instead of retaining the finite-field and positive quotient data;
it used the HasCompactification-selected adjunction instead of the supplied c; and
it did not identify the restricted unit/counit components. The final theorem binds
the actual D,l,E,n data, the separated finite-type scheme structure maps and f, the
chosen quasi-compact-open compactification and its nonnegative dimension bound.
`Conclusion` quantifies over the ordinary etale adjoint for exactly that c.
`Restriction` returns both preservation proofs and the lifted-functor adjunctions;
its homEquiv/unit/counit fields identify every arrow with the normalized class datum.
Its comparisons are precisely that datum's original comparisons, with identity and
cocycle equations on the constructible domains. The right side is fixed in the
normalization expressly used by the recorded dependency. All clauses of the node
are present and no unrestricted unbounded pro-etale adjunction is introduced.

I also checked the dependency records' alternative fixed-module interfaces: the
native finite-Tor predicate is expressly recorded there. This agrees with the
intrinsic finite-coefficient statement via the existing exact tensor realization
and constructible-origin theorem, not by redefining constructibility as a new
assumption. No missing prerequisite, new independent notion, or dependency repair
was required. All helper definitions construct actual lifts or assertion types;
the only postponed theorem is the named main theorem, matching this DAG node.
