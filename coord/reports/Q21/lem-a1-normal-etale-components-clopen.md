## Worker report

The item is stated as `AlgebraicGeometry.normal_etale_components_clopen` in
`Sheaf.AlgebraicGeometry.NormalEtaleComponentsClopen`. Its only theorem has proof `sorry`.
The module docstring cites Bhatt--Scholze, proof of Lemma 7.4.10, p. 71, first paragraph,
and Stacks 0BQ3/0357. The theorem docstring carries all seven DAG proof steps with their
inputs, including the pointwise finite-type criterion added by the stage-1 reviewer.
The node's statement, statement dependencies, proof and proof dependencies are unchanged.
No new nodes and no statement correction are needed.

Hypotheses and conclusions, checked against the entire node:

- Schemes X and Z and q:Z→X are `{X Z : Scheme.{u}}` and `(q : Z ⟶ X)`.
  There is no nonemptiness, compactness, connectedness, finiteness, surjectivity or
  separation assumption on either scheme or the map.
- X is locally Noetherian: `[IsLocallyNoetherian X]`, the recorded Mathlib class
  for `pqf-def-locnoeth`. Its affine-chart form agrees with the stated cover form.
- Every local ring of X is an integrally closed domain:
  `hnormal : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
  IsIntegrallyClosed (X.presheaf.stalk x)`. This is precisely the normal-domain inline
  form recorded by `def-weil-pbc-normal-ring`, not an integrally closed ring alone.
- q is etale: `[Etale q]`, the recorded scheme morphism class, not just formal etaleness.
- Local topological Noetherianness of Z:
  `∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧ TopologicalSpace.NoetherianSpace U`.
  U carries the subspace topology. Mathlib defines NoetherianSpace by ACC on opens;
  its `noetherianSpace_TFAE` identifies this with DCC on closed sets. The statement
  requires an open neighbourhood at every point, not a globally Noetherian space or
  a global finite set of components.
- Geometric unibranchness: for every `z : Z`, every `K H : Type (max u v)`, and
  the specified structures, `Algebra.StrictHenselizationPresentationIn.{u, v}
  (Z.presheaf.stalk z) K H → IrreducibleSpace (PrimeSpectrum H)`.
  `Field K`, its algebra over `IsLocalRing.ResidueField (Z.presheaf.stalk z)` and
  `IsSepClosure` give exactly the chosen separable closure. `Algebra (Z.presheaf.stalk z) K`
  and `IsScalarTower` require the structural map to factor through that residue field.
  `CommRing H` and `Algebra (Z.presheaf.stalk z) H` specify the strict-henselization algebra.
  The presentation premise is precisely the universal colimit and algebra identification
  in `def-sc-ring-strict-henselization`, not an arbitrary algebra or an assumption that its
  spectrum is irreducible. PrimeSpectrum is the underlying space of Spec H, and
  IrreducibleSpace includes nonemptiness. Quantifying over all presentations renders the
  node's strict-henselization formulation independently of any arbitrary choice, as
  required by proof step 4, which applies to any strict henselization.
- Every irreducible component is open and closed:
  `∀ C : Set Z, C ∈ irreducibleComponents Z → IsClopen C`.
  The recorded Mathlib definition is `{C | Maximal IsIrreducible C}`.
- Every connected component is irreducible and open and closed:
  `∀ C : Set Z, Maximal IsConnected C → IsIrreducible C ∧ IsClopen C`.
  Mathlib's IsConnected is nonempty and preconnected. Maximal is maximal with respect
  to subset inclusion. This states exactly the node's maximal nonempty connected
  subset convention without choosing a point or excluding the empty scheme.

Statement dependency declarations used:

- `def-pc-scheme`: Mathlib.AlgebraicGeometry.Scheme, `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`.
- `pqf-def-locnoeth`: Mathlib.AlgebraicGeometry.Noetherian,
  `AlgebraicGeometry.IsLocallyNoetherian`.
- `def-weil-pbc-normal-ring`: Mathlib.RingTheory.IntegralClosure.IntegrallyClosed,
  `IsIntegrallyClosed`, together with `IsDomain`, using the recorded inline conjunction.
- `def-weil-etale-morphism`: Mathlib.AlgebraicGeometry.Morphisms.Etale,
  `AlgebraicGeometry.Etale`.
- `def-sc-ring-strict-henselization`: the same defining colimit data as the recorded
  `Algebra.StrictHenselizationPresentation` in Sheaf.RingTheory.StrictHenselizationPresentation,
  with the authorized universe repair described below.
- `def-weil-irreducible-components`: Mathlib.Topology.Irreducible,
  `irreducibleComponents`, `IsIrreducible` and `Maximal`.
- `def-weil-connected-scheme`: Mathlib.Topology.Connected.Basic, `IsConnected`.
  The node's `ConnectedSpace` match gives connectedness of the whole space; for subsets
  its underlying Mathlib predicate IsConnected is exactly the same nonempty convention.

Proof dependencies are imported, with ordinary imports when only needed for the proof:
FinitePresentation, FiniteType and RingHomProperties for finite presentation/type and
`HasRingHomProperty.iff_exists_appLE`; Noetherian for
`LocallyOfFiniteType.isLocallyNoetherian` and `noetherianSpace_of_isAffine`; AffineScheme
and StructureSheaf for affine stalk localization; Sheaf.RingTheory.EtaleNormalRing for
`RingHom.Etale.isNormalRing`; LocalizationLocalization and the integral-closure import for
normal localization; Sheaf.RingTheory.PointedEtaleSmallFiltered for
`Algebra.pointedEtale_small_filtered`; Sheaf.RingTheory.StrictHenselizationLocalMaximalIdeal
for `Algebra.strictHenselization_local_maximalIdeal`;
Sheaf.RingTheory.EtaleColimitNormalLocalDomain for
`CommAlgCat.isDomain_isIntegrallyClosed_injective_of_etale_colimit`; Properties and
FunctionField for integral spectra; Sheaf.AlgebraicGeometry.RegularNormalDecomposition for
`AlgebraicGeometry.regular_normal_and_normal_decomposition`; Irreducible for component
restriction/injectivity and component existence/coverage. No import cycle is introduced.

Edge cases checked before writing:

- Empty Z: every pointwise assertion is vacuous; empty sets are neither irreducible nor
  nonempty connected, so both component assertions are vacuous as well.
- Empty X: a morphism to it forces Z empty; no artificial Nonempty hypothesis is added.
- Infinite disjoint unions of spectra of separable field extensions: locally Noetherian
  without quasi-compactness, and every singleton component is clopen. The statement
  permits an infinite component index and never claims global Noetherianness.
- The identity morphism: recovers the component statements for every locally Noetherian
  normal scheme; it requires no extra morphism property.
- A field and Spec Z: ordinary normal-base examples satisfy the hypotheses. A node or
  crossing of two branches is excluded because its local ring is not a domain.
- Strict-henselization spectrum: empty spectra are not erroneously called irreducible;
  the genuine universal pointed-etale colimit is local and nonzero by the cited proof.
- Size: v is independent of u, and all pointed-etale algebras are in Type (max u v).
  This includes the original same-universe case and larger universes; the index category
  contains the base algebra and cannot become vacuous by being smaller than its base.

Searches (2026-10-18):

- msearch leansearch: "An etale scheme over a locally Noetherian normal scheme has open
  irreducible components". Eight hits, including NoetherianSpace component interiors,
  finite_irreducibleComponents_of_isNoetherian, Scheme.Etale and integral-scheme facts;
  none states all four clauses under these hypotheses.
- msearch leanfinder: "An etale scheme over a locally Noetherian normal scheme has clopen
  irreducible components and irreducible strict henselization spectra". Eight hits:
  Scheme.Etale, algebra etale-locus facts, IsIntegral and integral irreducibility; no match.
- msearch loogle: `"irreducibleComponents", "IsClopen"`. Zero hits.
- msearch grep in AlgebraicGeometry: `geometrically.?unibranch|irreducibleComponents.*[Oo]pen|
  [Ee]tale.*[Nn]ormal`. Two hits (component preimage and geometrically irreducible morphism
  component equivalence), neither this statement.
- rg of the named upstream WeilConjectures and project lean/Sheaf trees using etale/normal
  and unibranch/clopen-component terms, and upstream grep of the item id: no exact match.
  The targeted follow-up `unibranch|clopen irreducible|irreducibleComponents.*IsClopen|
  normal_etale_components_clopen` found only NormalGeometricCoverComponents's proof reference
  to this item. That theorem requires a connected quasi-compact base and a valuation
  lifting property and asserts finite-etale geometric-cover components; it is not this item.
- rg of Mathlib NoetherianSpace, Connected.Basic, Irreducible, Scheme, Noetherian, Etale
  and IntegrallyClosed sources located the recorded primitive notions and their full
  signatures/docstrings, which were read.
- rg of both project source trees and dag/lean_names_upstream.json for the proposed
  StrictHenselizationPresentationIn and pointed-diagram names found no existing declaration.

Sources read locally: the entire assigned node and its seven statement dependencies;
the recorded declaration modules and proof dependency records; Bhatt--Scholze PDF p. 71;
Stacks properties.tex normal-geometrically-unibranch and normal-locally-finite-nr-irreducibles.
There is no STATEMENT-DISPUTED issue or mathematical node fault.

Both supplied modules compile independently in dependency order through scompile.py,
under the default limit, with no errors or warnings. No global build or direct git command
was run, and all authored files are confined to the sandbox.

## Dependency modules

`def-sc-ring-strict-henselization` receives a lean-only §1(B) repair, in
Sheaf.RingTheory.StrictHenselizationPresentationIn. The previous recorded structure
has `(A K H : Type u)`. Using it with a Type u stalk and Type (max u v) strict-henselization
algebras fails elaboration: inferred u rejects K, while explicitly supplying max u v
rejects the stalk. Silently setting v=u would lose the arbitrary larger-universe cases.

The repaired structure `Algebra.StrictHenselizationPresentationIn` has A : Type u and
K,H : Type (max u v), and its diagram ranges over CommAlgCat.{max u v} A. It retains
exactly the category of etale A-algebras pointed by A-maps to K, its forgetful diagram,
a cocone, its IsColimit proof, and a specified A-algebra identification with H. The
pointing cocone and induced residueMap are real constructions by Over.w and colimit
descent; there is no sorry in any definition and no choice of an unspecified object.
At v=u the diagram is definitionally the original diagram, and the structure has exactly
the original three fields, so the two presentations convert by copying those fields.
This is the same notion, generalized in size; the original module is imported and all
old declarations remain available. The repaired lean record lists every new declaration,
retains the dependency's mathematical statement and all other fields, and explains why
its previous interface was unusable. The item itself successfully compiles as a consumer
with independent u and v; its elaborated statement tests precisely this repaired interface.

## Second reading by Q21

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
