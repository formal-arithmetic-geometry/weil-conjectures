## Worker report

The module `Sheaf.Paper.ConnectedAdicIntegralBasis` states
`WeilConjectures.connected_adic_integral_basis`, with `sorry` as its entire proof.
Its only helper, `connectedAdicScalarRingMap`, forgets commutativity in the recorded
canonical completed coefficient inclusion; its data are the actual sheafCompose map.
No new node, dependency repair, or statement correction is needed.

Hypothesis-by-hypothesis correspondence:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Finite p-adic fields E and L: the two `Field`, `Algebra ℚ_[l]`, and
  `FiniteDimensional ℚ_[l]` instances. The inclusion is the algebra homomorphism
  `ι : E →ₐ[ℚ_[l]] L`; it is injective because its source is a field.
- Compatible extending absolute values, valuation rings, and chosen uniformizers:
  `Padic.coefficientExtensionAbsoluteValue`, `coefficientExtensionIntegers`, and
  `coefficientExtensionUniformizer` from the dependency's coefficient construction.
  The absolute values are the unique spectral extensions. Their compatibility is
  `integralScalar_absoluteValue`. The integer inclusion is
  `integralScalarIntegerInclusion l E L ι`, the restriction of the given embedding.
- Connected X: `(X : Scheme.{t}) [ConnectedSpace X]`, which includes nonemptiness.
- Small pro-etale site: `Scheme.ProEt.topology X`, with objects in Type (t+1) and
  morphisms in Type t. Coefficient fields have independent universe u. All sheaves
  and module values have size `max u (t+1)`; no equality of site and coefficient
  universes is assumed.
- Finite quotients and completion are the recorded
  `integralCoefficientSheaf l H X n` and
  `completedIntegralCoefficientSheafUnrestricted l H X`. Natural n indexes the
  positive exponent n+1, so it covers every n >= 1 in the node.
- The coefficient map is `completedIntegralScalarCoefficientMap l E L ι X`;
  `connectedAdicScalarRingMap` merely gives it the RingCat interface for modules.
- The prescribed d is `completedScalarRelativeDegree l E L ι = [L:E]`, with
  the E-algebra structure induced by ι. The arbitrary tuple β has index `Fin d`.
  Its integral-basis hypothesis is exactly bijectivity of
  `a ↦ ∑ i, integralScalarIntegerInclusion ... (a i) * β i`, i.e. existence and
  uniqueness of every expansion. This avoids assuming an unrelated module action.

Conclusion-by-conclusion correspondence:

- `∃ eE eL` gives the two ring equivalences from the actual integer rings to the
  sections of their completed ring sheaves over `op (Scheme.ProEt.mk (𝟙 X))`.
  This is evaluation at X, the final site object, hence global sections.
- The first two conjuncts fix `eE a` and `eL a` to `integralScalarConstant`.
  These are the recorded unique compatible constant residue sections, not an
  arbitrary abstract isomorphism.
- The next two conjuncts give every projection of `eH a` as
  `integralScalarFiniteConstant`, which is the sheafification-unit image of the
  actual residue of a modulo the chosen uniformizer to exponent n+1.
- The fifth conjunct is exactly `c_X (eE a) = eL (j a)` for the actual inclusion j.
- For every prescribed β satisfying the unique-expansion hypothesis, `∃ Φ`
  is an isomorphism from the finite product of d copies of the coefficient unit
  module to the target unit module restricted along c. This finite product is
  the finite direct sum in the node's abelian category.
- `∀ U x` specifies Φ on every section as the sum of the images under c of the
  `Pi.π` coordinates, multiplied by `integralScalarConstant ... (β i)`.
  This fixes the actual map and all columns, not merely its isomorphism class.
- `∀ U n i` identifies all projections of those columns with the constant residue
  sections of the prescribed β_i. At U=X they are precisely eL(β_i), by the
  normalization conjunct above.
- The last `∀ x` gives the global-section formula explicitly: Φ(x) is eL applied
  to the original integral linear combination of β with coefficients obtained by
  applying eE.symm to each coordinate. Since eE,eL are equivalences and the integral
  combination map is bijective, this says exactly that the two bases coincide.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, reexporting the coefficient extension
  construction and its chosen integer rings, uniformizers, and quotient rings.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` (nonempty included).
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.mk`,
  `ProEt.topology`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses` and its constant quotient cone; this
  reexports the actual completed coefficient sheaf and its projections.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`, the
  sheafification of the constant presheaf.
- `Sheaf.Paper.CompletedIntegralScalarData`:
  `completedIntegralScalarCoefficientMap`, reexporting `completedCoefficientMap`,
  `completedScalarRelativeDegree`, `integralScalarIntegerInclusion`,
  `integralScalarFiniteConstant`, and `integralScalarConstant` from
  `FiniteFreeCompletedScalarComparison` and `IntegralScalarExtensionWellDefined`.
  The constant section is characterized uniquely by all finite residues; the
  coefficient map is characterized uniquely by all quotient inclusion squares.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, the transparent
  abbreviation of Mathlib's `SheafOfModules`, reexported by the dependency modules.
  `SheafOfModules.unit`, `restrictScalars`, and the product/Pi projections are the
  existing Mathlib constructions, not a private module-sheaf category.

The modules of all recorded proof dependencies are imported (proof-only imports
are non-public). The proof docstring follows the four DAG steps: finite constant
sections and connectedness; sectionwise limits and rank-one completeness;
compatibility of the genuine coefficient inclusion; the supplied prescribed-basis
adic-limit lemma and its global-sections formula.

Sources read: the actual PDF, printed p.30, Lemma 4.2.12 and its proof; pp.58-59,
Definition 6.8.1 and Lemma 6.8.2(1) with its proof. The continuous-function model
and its inverse-limit identity are exactly the source constructions. No qcqs
hypothesis is needed for the discrete assertion or for the connected specialization.

Edge cases checked before writing: empty X is excluded by ConnectedSpace; arbitrary
nonempty connected X need not be reduced, affine, or qcqs. Identity E=L and any
prescribed integral unit basis remain included. Ramified extensions are included:
the actual quotient inclusion is used, without identifying the uniformizers or
assuming that ramification index is one. Level n=0 means positive exponent one;
no zero quotient level is accidentally substituted. The universal Fin d basis
condition does not silently choose a different basis. No characteristic restriction
on X is present in either the node or this theorem. Independent t,u permit
coefficients larger or smaller than the scheme.

Searches actually run with msearch.py for Q18 and this item:

- leansearch: "Global sections of completed integral coefficient sheaves on a
  connected proetale scheme and prescribed finite free integral basis". Eight
  results included Sheaf.Γ, Scheme.ΓSpecIso, HasGlobalSectionsFunctor, and
  SheafOfModules.sections; none is the completed connected coefficient assertion.
- leanfinder: "An integral basis induces an isomorphism from a finite free
  completed constant sheaf to the restriction of scalars on a connected scheme".
  Eight results included IsIntegralClosure.module_free,
  FiniteDimensional.exists_is_basis_integral and a condensed singleton comparison;
  none states the required normalized completed-sheaf comparison.
- loogle: "AlgebraicGeometry.Scheme.ProEt". Twelve hits locate the site and its
  topology, not this statement.
- grep: "completed.*basis|basis.*completed|[Cc]onnected.*constant". Twenty-five
  Mathlib hits concern connected categories, locally constant functions, and
  topology; none covers the full completed coefficient/basis assertion.
- Direct rg of lean/WeilConjectures and lean/Sheaf for the item id and
  `connected_adic_integral_basis|connectedAdicScalarRingMap` found no declaration.
  Keyword rg of both source roots found the existing completed scalar and constant
  section APIs above. The point-specific PointFiniteFreeSectionsTensor structure
  only handles Spec k, and chooses a basis existentially; it does not state this
  arbitrary-connected-scheme, every-prescribed-basis assertion. The general
  AdicBasisLimit is a proof input and has no connected global-section equivalences.

Validation: scompile.py compiled the sandbox and library module separately, with
no errors or warnings. There is one intentional theorem sorry; no definition has
postponed data. No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by Q18

I reread the node and the completed file clause by clause after the successful
server compile. This is a second pass by this dispatcher-started worker; no other
agent was started, as explicitly required by the brief. The maintainer's independent
review remains the independent reading.

The two field hypotheses, algebra embedding and ConnectedSpace binders match the
objects of the node. The chosen uniformizers and unique extending absolute values
are precisely those of its recorded coefficient definition. The two explicit
constant normalizations prevent exchanging the intended ring maps for arbitrary
ring equivalences. Both projection conjuncts cover every positive level. The
compatibility conjunct uses the actual field embedding restricted to integers.
The basis quantifier is universal, and its bijective expansion hypothesis supplies
exactly uniqueness and existence, without a second algebra structure. Φ points
from the finite free source to the restriction of R_L and its formula uses that
same c at every site object. The column-residue conjunct and final global-section
formula retain the node's final two clauses. No hypothesis or conclusion was
changed in this reading. I also rechecked line widths, explicit universe/variable
binding, and that the helper only forgets commutativity of the canonical map.
