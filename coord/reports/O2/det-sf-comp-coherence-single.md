## Worker report

The module `Sheaf.Paper.CompactificationLocalizing` states
`AlgebraicGeometry.ProEtale.CondensedRing.compactification_localizing`, with a single
`sorry` proof. It uses the existing compactification functor and existing definitions
of Dctf and its localizing closure. No definition, axiom, or new node is introduced.

The shared checkout acquired an N3 `lean` binding during this worker's reading.
That module was read in full. Its inline coefficient disjunction is not the exact
current statement: its last case uses `Profinite.padicAlgClRingObj`, whose source
explicitly excludes continuous maps not contained in one finite subextension.
The present item and its recorded coefficient dependency instead specify the topology
of the algebraic closure itself. This delivery retains the declaration and all four
conclusions, and replaces the inline disjunction by the recorded
`IsLocalizingAdmissibleCoefficient ℓ Λ`. In particular no second notion of admissibility
is defined. The DAG statement itself is unchanged; only its `lean` field is changed.

Hypotheses, clause by clause:

- A prime ℓ is `(ℓ : ℕ) [Fact ℓ.Prime]`. The field is `(k : Type u) [Field k]`.
  `[Fact (ringChar k).Prime]` expresses positive characteristic, since the
  characteristic of a field is zero or prime. `[Fact (ringChar k ≠ ℓ)]` expresses
  the stated inequality of characteristics. These exclude characteristic zero
  and characteristic ℓ, without excluding any allowed positive characteristic.
- A commutative condensed coefficient is
  `(Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ]`. `_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ` supplies exactly
  the finite discrete power-of-ℓ-torsion, ℤ_ℓ, ℚ_ℓ, finite extension E, valuation
  ring O_E, and topological algebraic-closure cases. It is invariant under ring
  object isomorphism, so it does not force a particular representative of a ring.
- `X Y : Scheme.{u}` have `Over (Spec (.of k))` instances. For each scheme,
  `LocallyOfFiniteType` and `QuasiCompact` of its structure map express finite
  type over k; `IsSeparated` of that map expresses separatedness over k.
- `[CompactSpace Y] [QuasiSeparatedSpace Y]` explicitly express that Y is qcqs.
  They are already consequences of the standing finite-type separated setting,
  so their inclusion does not restrict the mathematical cases.
- `(f : X ⟶ Y) [f.IsOver (Spec (.of k))]` is a k-morphism.
  `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]` express the stated
  separated finite-type hypothesis on f.
- `c : Compactification.BoundaryCompactification f` is the dependency's existing
  compactification notion. Its object `c.obj.obj : Compactification f` supplies
  the middle scheme, its open map `i`, its proper map `g`, and `f = i ≫ g`.
  The full-subcategory membership supplies quasi-compactness of `i`.
  A wide-subcategory object imposes no condition concerning any refinement;
  in particular no density hypothesis is imposed. Its morphism definition has
  no effect on the quantification over objects here.
- The specified ambient functor is
  `rightDerivedLowerShriekOfCompactification Λ c.obj.obj`. Its definition is
  levelwise derived exact extension by zero followed by the total right
  derived functor of module-object pushforward. Thus it is precisely Rp_* j_!,
  not the right derived functor of an underived composite.

Conclusions, clause by clause:

- The first conjunct universally quantifies over ambient K and maps
  `localizingClosureProEtale Λ X K` to the target closure predicate of the
  specified functor's image. It is exactly the objectwise condition allowing
  restriction to the full subcategories, with the ambient map action retained.
- The second conjunct sends every distinguished triangle whose three vertices
  belong to the source closure to a distinguished triangle, via the existing
  functor's `mapTriangle` and its canonical shift comparison. These full
  triangulated closures inherit their triangles from the ambient category;
  hence this is exactly triangulated exactness of the restriction.
- The third conjunct quantifies over every `I : Type (u + 2)` and every discrete
  ambient diagram K whose vertices lie in the source closure, and asserts
  `PreservesColimit K` for the specified functor. The ambient unbounded derived
  category has object universe u+2, the indexing universe used by the recorded
  `IsLocalizingSubcategory` definition. This is preservation of precisely the
  ambient coproducts defining the closure, not merely finite or countable sums.
- The fourth conjunct maps `constantModelBoundedConstructible Λ X K ∧
  DerivedCategory.finiteTorAmplitude _ K` to the identical two properties on Y
  for the specified image. These are exactly Dctf on the two schemes, using
  the finite constant scalar model convention of the recorded dependency.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `CondensedRing.compactificationOverField` and the standing explicit scheme
  setting, read along with its chosen compactification convention. The item
  quantifies over every given compactification, rather than replacing it by
  this chosen one.
- `Sheaf.Paper.CondensedConstantConstructibility` (publicly imported through the
  localizing module): `IsConstantModelConstructible`,
  `constantModelBoundedConstructible`, `ConstantModelConstructibleFiniteTor`.
- `Sheaf.Paper.LocalizingAdmissibleCoefficients`:
  `IsLocalizingAdmissibleCoefficient`, which publicly imports
  `Sheaf.Paper.LocalizingClosure`: `CategoryTheory.IsLocalizingSubcategory`,
  `CategoryTheory.localizingClosure`, `ProEtale.localizingClosureProEtale`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`:
  generic `Functor.rightDerivedFunctor` of the underived `CondensedRing.lowerStar`
  composite and `CondensedRing.derivedUpperStarLowerStarAdjunction`; these enter
  through the lower-shriek module.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek`:
  `CondensedRing.rightDerivedLowerShriekOfCompactification`, whose full source
  and docstring were retrieved with `scompile.py --source`.
- `Sheaf.Compactification.BoundaryRefinement`:
  `Compactification.QuasiCompactObjects` and `BoundaryCompactification`.
- Mathlib morphism modules: `LocallyOfFiniteType`, `QuasiCompact`, `IsProper`,
  `IsSeparated`, `QuasiSeparated`; `CompactSpace` and `QuasiSeparatedSpace`
  give the corresponding absolute scheme properties.
- The stated proof dependency `Sheaf.Paper.OpenImmersionLocalizing` is imported
  without `public`. The proper-image proof dependency currently has no Lean
  binding, so it is not imported or independently restated.

Source and proof-plan check: read the main-20261015 node and its three-paragraph
proof. The docstring carries each of the extension-by-zero, proper-image, and
composition steps. There is a proof-dependency convention discrepancy to retain
for review: `det-proper-image-localizing-proper` currently specifies the
finite-subextension algebraic-closure coefficient, whereas this node and its
recorded admissibility definition specify the actual topological algebraic
closure. Its proper-image application in that case requires a suitable
comparison or the appropriate coefficient theorem at proof stage. This
statement does not add that comparison or a preservation assumption as a
hypothesis. There is no established counterexample to the item's own statement.

Edge cases checked: the empty indexing type is included, giving preservation of
the zero coproduct; zero complexes and zero modules are included. No nonzero
coefficient-ring hypothesis is imposed, so the finite zero ring remains allowed.
Empty schemes and non-dense compactifications are allowed. Proper maps with
identity open part and quasi-compact open immersions with identity proper part
are instances of the same statement. Neither the algebraic closure nor the
integral coefficients are replaced by a discrete or derived-complete category.
All universes and variables are explicit and `autoImplicit` is disabled.

Searches for an existing exact declaration:

- `msearch.py ... leansearch`: “Compactification derived pushforward after
  extension by zero preserves constructible finite Tor objects and coproducts
  in their localizing closure”. Eight hits: compact support of ordinary
  functions, exact derived functor factorization, finite product/colimit
  localization facts. None states this geometric preservation theorem.
- `msearch.py ... leanfinder`: “Compactification extension by zero followed by
  proper derived pushforward restricts to an exact coproduct preserving functor
  on the localizing closure of bounded constructible finite Tor complexes”.
  Eight hits: condensed solid modules, derived Ext maps, and homological
  localization. No match.
- `msearch.py ... loogle`: `CategoryTheory.Limits.PreservesColimitsOfShape,
  CategoryTheory.Functor.comp`. Twelve hits; `comp_preservesColimitsOfShape`
  supplies only the elementary composition step, not this geometric theorem.
- `msearch.py ... grep`: `localizing|[Cc]ompactification|[Ll]owerShriek` in
  Mathlib CategoryTheory. Six hits, concerning Verdier localizing classes and
  over-site topologies, not this theorem.
- `rg` in upstream WeilConjectures and side `lean/Sheaf` for the item id and
  compactification/localizing patterns found the existing N3 module and its
  exceptional-adjoint consumer. The module was read in full and cannot be
  recorded `existing: true` for the current coefficient clause for the reason
  explained above. The source definition of `padicAlgClRingObj` in EllAdic.lean
  was read to verify that difference. All actual search outputs are retained
  by the prescribed launcher in the sandbox search log.

Validation: the prescribed scompile.py wrapper compiled both its sandbox probe
and the library-path module cleanly (4.2 and 5.4 seconds), with no errors or
unexpected warnings. No global build or direct git command was run.

## Second reading by N2

This is the author's separate second reading; the dispatcher forbids starting
another agent, and the maintainer supplies the independent review. Reopened
the complete node, the finite-constant constructibility definition, the closure
definition, the admissibility definition, the compactification structure, and
the delivered signature. Checked every hypothesis against the list above.
The positive characteristic Fact excludes exactly zero characteristic and the
second Fact excludes ℓ. The wide-subcategory encoding does not impose density
or select a special compactification. The four conjuncts respectively give
restriction, exactness, all ambient sums in the closure's own indexing universe,
and both parts of Dctf. The only mismatch in the pre-existing module was the
inline coefficient convention, repaired by using the dependency's actual
predicate. This re-reading found no further signature change necessary. The
source-based proof-dependency discrepancy is explicitly reported above rather
than silently identifying the two algebraic-closure objects.
