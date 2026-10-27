## Worker report

The module `Sheaf.Paper.FiniteExceptionalCompositorCoefficients` states finite
coefficient compatibility for the canonical exceptional compositor, including both
explicit common-transpose equalities. The sole postponed proof is
`WeilConjectures.FiniteExceptionalCompositorCoefficients.finiteExceptionalCompositorCoefficients`.
The other declarations are real formula definitions belonging to this statement.

Clause-by-clause correspondence:

- The finite-field datum is `D : FiniteFieldDatum`; its `p`, `a`, `q`, finite field
  `k₀`, algebraic closure `k`, and cardinality identity give the specified geometric
  field. `B : D.CoefficientDatum` supplies the prime `B.l`, `B.different`, and fixed
  algebraic closure of the l-adic field. The bundled finite extensions are `E` and
  `L : FieldStage B.l`; their existing coefficient rings use the valuation ring
  and its chosen uniformizer. Positive levels are `n m : ℕ+`.
- `X Y Z : SixFunctorSpace D` are finite-type schemes over that very field:
  the full over-category predicate is locally of finite type and quasi-compact.
  The three `IsSeparated ...obj.hom` instances require separated structure maps.
  `f` and `g` are morphisms in that over category, hence k-morphisms. Their
  `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact` hypotheses are exactly
  separated finite type. The composite is `(f ≫ g).hom.left`.
- `P Q R : System ...` are presentations of the dependency's specified operations
  at every coefficient stage for f, g and x. They retain actual pro-etale categories,
  finite etale-adjoint realizations, completed integral, raw rational and common
  stages, and coefficient/refinement normalizations. These are the datum fixed in
  the node, not an extra ambient pro-etale adjoint assumption.
- `cf cg cx` are arbitrary compactifications of those three maps. `finiteAlpha`
  is the previously recorded canonical compactification compositor restricted
  through the fully faithful finite-Tor inclusion, using `S` and `S'` at the two
  finite coefficient stages. Its construction uses the inverse of the operation
  datum's oppositely oriented compositor. No arbitrary alpha is assumed by the
  theorem. `exceptionalIso` is literally `conjugateIsoEquiv` of inverse alpha,
  with the composite and direct constructible adjunctions.
- `FiniteChange` enumerates exactly the finite maps in this item: quotient with
  m ≤ n; retained extension with ramification ideal equality and target level en;
  extension followed by any positive quotient m ≤ en. Its last equality pins the
  actual ring-sheaf maps, retaining their composition. This is an inline index
  predicate for this node's coefficient list, not a second construction of rings
  or derived scalar extension.
- `TX TY TZ : Scalar ... a ...` present the same displayed derived tensor
  functors at all three vertices, through `Scalar.realization`. Shared endpoint
  presentations avoid silently identifying independently presented scalar
  functors. `df dg dx : Comparison ...` supply q and counit-normalized b. The
  hypotheses `_hf _hg _hx : QNormalized ...` say q is precisely the canonical
  proper/open scalar-adjunction mate through `P/Q/R.ring.left`, not any chosen
  isomorphism. `Comparison.counit` uniquely determines b as the transpose of
  inverse q followed by C(epsilon). These hypotheses spell out the fixed maps
  of the node; they do not assume its composition square.
- `Compatibility` quantifies over every `L : C ... Z (.finite E n)`.
  Its first conjunct equates `leftMap = TX.map(c_A) ≫ b_x` and
  `rightMap = b_f ≫ G_f,B.map(b_g) ≫ c_B`, exactly the main display, written
  in Lean's forward composition order.
- Its second and third conjuncts apply the inverse Hom equivalence of the
  specified x-adjunction to each side separately and identify each with
  `commonTranspose`. The latter is inverse alpha_B, then F_g,B(inverse q_f),
  then inverse q_g, then C_Z of the composite counit. The two middle maps are
  precisely inverse q_{g,f}. `Adjunction.comp_counit_app` identifies the last
  counit with F_g,A(epsilon_f,A) followed by epsilon_g,A, so this is exactly
  the displayed C_Z(beta_A) q_{g,f}^{-1} alpha_B^{-1}.
- All constituent maps are natural transformations or images of their components;
  equality at every L is their natural-transformation equality. No quotient
  flatness premise occurs. The scalar realization is derived extension throughout.
  Integral/rational/common stages form the surrounding datum; the conclusion here,
  as in the node, concerns its listed finite coefficient changes.

Dependencies used:

- `sk-def-sf-setting`: published
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`, together with its
  constructibility and Tor-amplitude public imports. Its etale definitions were
  read; this item's pro-etale finite-Tor realization is the recorded `C` of the
  exceptional-adjunction dependency, not a private copy of that etale category.
- `sk-def-sf-operations`: `Sheaf.Paper.SixFunctorOperationDatum`,
  `WeilConjectures.SixFunctorOperationDatum`, whose finite support and composition
  are normalized to the actual pro-etale compactification operations.
- `lem-sf-constructible-exceptional-adjunction-coefficients`:
  `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` and its public
  data module: `FieldStage`, `Stage`, `C`, `Operation`, `Comparison`, `Scalar`,
  `QNormalized`, `System`, and `exists_system`. In particular, `Comparison.counit`
  is the required b normalization and `Scalar.realization` is derived tensor.
- `def-weil-pbc-adjunction-conjugate`: Mathlib's `CategoryTheory.conjugateEquiv`
  and `conjugateIsoEquiv` in `Mathlib.CategoryTheory.Adjunction.Mates`.
- `thm-sf-comp-composition`: `AlgebraicGeometry.ProEtale.originComposition` in
  `Sheaf.Paper.CanonicalOriginCompactSupportComposition`, the ambient origin
  compositor used by the recorded operation normalization and `finiteAlpha`.
- `def-sf-finite-exceptional-compositor-maps` owns the existing `finiteInclusion`,
  `finiteLeft`, `finiteAlpha`, and `exceptionalIso` definitions in
  `Sheaf.Paper.ConstructibleExceptionalCompositor`, namespace
  `WeilConjectures.ConstructibleExceptionalCompositor`. The module is imported
  directly. The theorem conclusion of `lem-sf-constructible-exceptional-compositor`
  is not a statement prerequisite.
- Proof-only imports retain `Sheaf.SixFunctors.CompactCoefficientComposition`
  (both actual finite coefficient composition statements) and
  `Sheaf.Paper.FiniteFreeCompactComposition` (`finiteLevelComposition` and
  `systemComposition`). The composite-adjunction and adjunction-mate proof
  dependencies are Mathlib `Adjunction.comp` and `mateEquiv`, imported publicly
  through the compositor module. Their signatures, counit formula and docstrings
  were read.

Edge cases checked before writing: identity quotient m=n; n=m=1; identity geometric
morphisms; empty schemes; zero complexes; trivial coefficient extension; arbitrary
ramification e>1 (target is en, never silently n); any subsequent m between 1 and en.
The positive indices match the source and exclude only its forbidden level zero.
No smoothness, properness, flatness of quotients, or ambient exceptional adjoint
is added. All universes and variables are explicitly bound, with autoImplicit and
relaxedAutoImplicit disabled. Site morphism/object universes are inherited unchanged.

Searches made:

- msearch leanfinder: “Finite coefficient change commutes with the canonical
  compositor of exceptional inverse image functors on constructible sheaves”.
  Eight hits: locally constant sigma comparison, constructible-spectrum maps,
  Scheme.Modules.restrictFunctorComp and its component lemmas,
  LightCondensed.ihomPoints_symm_comp, and pushforwardComp_inv_app_app.
  None states this coefficient/exceptional composition theorem.
- msearch loogle: “CategoryTheory.conjugateEquiv, CategoryTheory.mateEquiv_hcomp”.
  Zero hits for the combined query. Direct source reading finds the generic
  mate/conjugation infrastructure, not this geometric result.
- msearch leansearch: “Counit normalized coefficient change commutes with right
  adjoint conjugates of composition”. Eight hits include counit naturality,
  functorialityCounit, conjugateEquiv_counit, and rightAdjointUniq_hom_counit.
  None supplies the specified geometric left compositor coefficient square.
- msearch grep: `conjugateEquiv|mateEquiv_hcomp`, Mathlib
  `CategoryTheory/Adjunction`: twelve hits in CompositionIso, Unique, and Mates.
  These provide generic facts only.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for the node id and
  `finiteExceptional.*[Cc]oeff|exceptional.*[Cc]omposition.*[Cc]oeff`:
  no declaration for this node. The closest result in
  `FiniteAdjointMateCompatibility` has smoothness hypotheses, quotient-only
  etale coordinates and lacks the two explicit transpose assertions, so is not
  an exact existing match. Broader compositor searches located the canonical
  `finiteAlpha`/`exceptionalIso` interface now reused here.

The original natural-language statement is preserved verbatim. The repair adds
the definition-ownership node described below; no dependency theorem is restated.

Additional exact-name Loogle search `CategoryTheory.conjugateEquiv` returned twelve
generic conjugation, identity, isomorphism and unitor declarations in Mathlib Mates;
none is the geometric coefficient statement.

Validation: scompile.py compiled the complete delivered module in both sandbox and
library modes, with no errors or unexpected warnings. Explicit Scalar.commShift
arguments retain the recorded structures without an extra hypothesis or local instance.

## Repair of returned delivery f98d7b5ad50c

H2 is repaired by replacing the added theorem dependency
`lem-sf-constructible-exceptional-compositor` with
`def-sf-finite-exceptional-compositor-maps`. The latter owns all four constructions
used from the published module. The module import now names this ownership in a
comment. The reviewed mathematical statement, definitions, proof docstring and
all hypothesis/clause correspondences above are unchanged. The current base node
was compared field by field: only `lean` and the added definition dependency differ.

## New nodes

`def-sf-finite-exceptional-compositor-maps` is a definition node with `existing: true`
for `Sheaf.Paper.ConstructibleExceptionalCompositor`. Its four declarations are:

- `finiteInclusion`: the finite-Tor full-subcategory inclusion, with no extra data.
- `finiteLeft`: the unique fully faithful lift of the specified compact-support
  realization comparisons, for one separated finite-type morphism.
- `finiteAlpha`: the unique lift of the pasted normalized compactification
  composition, for two separated finite-type morphisms and their composite.
- `exceptionalIso`: the literal `conjugateIsoEquiv` of inverse alpha, using the
  composite and direct constructible adjunctions at the same stage.

Its statement introduces the datum, positive level, schemes, maps, normalized
systems, compactifications, operations and adjunctions explicitly. Its dependencies
are the recorded setting, operations, constructible-adjunction interface, canonical
compact-support composition and adjunction-conjugation nodes. The blueprint source
is the current Verdier-exchange proof's complement and final compatibility clause.
The four definitions have real construction data already published; no new proof
or choice of a compositor is introduced. Identity morphisms, empty schemes, zero
objects and level one remain admitted; no Tor condition is forgotten except by
the explicitly specified inclusion. The generic conjugate definition retains all
coefficient stages, though the consumer only uses finite stages.

Ownership searches: LeanSearch for canonical compact-support composition restricted
to finite-Tor categories returned compactly-supported-map topology declarations;
LeanFinder for full-subcategory lifts and conjugateIsoEquiv returned generic lift
infrastructure; Mathlib CategoryTheory grep for the four exact names returned no
hits. Project rg located the exact four definitions in the existing module;
DAG definition-record scanning found no owner of that module. Blueprint search
for `exceptional compositor` returned zero matches. The queries and returned names
are recorded individually in the new node's `mathlib_searches`.

Repair validation: scompile.py compiled the delivered module again in sandbox and
library modes, with no errors or unexpected warnings. The prescribed dry run also
checks existing-declaration probes for the four definitions in the new owner.

## Second reading by N9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
