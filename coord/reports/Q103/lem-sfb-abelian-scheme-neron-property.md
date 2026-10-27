## Worker report

The module Sheaf.AlgebraicGeometry.AbelianSchemeNeronProperty states
AlgebraicGeometry.abelianScheme_neron_mapping_property, with sorry as its sole
proof. No definitions, helper theorems, dependency repairs, or new nodes are
needed. The existing node is changed only in lean.

Source read: BLR, Néron Models, 1.2 Definition 1 (printed p.12) and Proposition 8
with its proof (printed p.15, PDF p.21), in the primary scan at
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf.
The proposition treats an abelian scheme and arbitrary smooth test schemes.
The docstring follows the four steps of the DAG proof: reducedness/dominance and
separated uniqueness; proper extension on a big open of each affine chart;
relative Weil extension; agreement and gluing on an arbitrary open cover.

Hypothesis and clause correspondence:

- D is a Dedekind domain: D : Type u, CommRing D and IsDedekindDomain D.
  Mathlib's class allows dimension zero, so hD : ringKrullDim D = 1 retains
  the node's explicit dimension-one convention. The class supplies domain,
  Noetherianity and integral closedness, with dimension at most one.
- E is its fraction field: Field E, Algebra D E and IsFractionRing D E.
- T is a nonempty open subscheme of Spec D: T : (Spec (CommRingCat.of D)).Opens
  with Nonempty T; its scheme is T.toScheme and its inclusion is T.ι.
- B over T: B : Over T.toScheme. Its group diagrams are GrpObj B; the
  commutativity diagram is IsCommMonObj B. The group object uses the standard
  Cartesian monoidal structure on Over, whose products are fibre products.
- Smooth and proper: Smooth B.hom and IsProper B.hom. The latter already
  includes IsSeparated, whose diagonal is an IsClosedImmersion. No redundant
  separatedness hypothesis is added.
- Connected fibres: hB : ∀ t : T.toScheme, ConnectedSpace (B.hom.fiber t).
  These are the actual scheme-theoretic residue-field fibres. They are
  nonempty because of the group identity section; ConnectedSpace therefore
  adds no nonemptiness beyond the node's group-scheme hypothesis.
- Every smooth T-scheme X: X : Over T.toScheme with Smooth X.hom. There is
  no quasi-compactness, finite-type, separatedness, connectedness or
  nonemptiness hypothesis on X.
- Hom_T(X,B) is X ⟶ B in Over T.toScheme; f is an arbitrary scheme morphism
  over T, without a group-homomorphism constraint on f or any group law on X.
- Generic restriction is fun f ↦ (Over.pullback
  (Spec.map (CommRingCat.ofHom (algebraMap D E)))).map ((Over.map T.ι).map f).
  Over.map T.ι composes the structure maps with the inclusion into Spec D;
  Over.pullback then takes their fibre products with Spec E, including the
  canonical map on those fibre products. Its codomain is the E-morphisms
  between those pulled-back objects, exactly Hom_E(X_E,B_E).
  The fraction-field spectrum maps to the generic point of Spec D, which is
  in every nonempty open T. Thus T ×_{Spec D} Spec E is canonically Spec E;
  pullback pasting identifies the displayed fibres and map with the fibres
  and restriction taken over T in the node. This is a canonical computation
  of the same base change, without adding an arbitrary generic-point map or
  a factorization hypothesis. Function.Bijective states both existence and
  uniqueness of extensions.

Dependency declarations read and reused:

- def-pc-scheme and def-weil-affine-spectrum:
  Mathlib.AlgebraicGeometry.Scheme, AlgebraicGeometry.Scheme,
  Scheme.Hom, Spec and Spec.map.
- def-pc-base-change:
  WeilConjectures.AlgebraicGeometry.BaseChangeConventions. Its record explicitly
  instructs scheme and morphism base change to use CategoryTheory.Over.pullback;
  that declaration's definition and the module's
  AlgebraicGeometry.baseChange_morphism_projections were read. The module is
  publicly imported, with its inherited scheme fibre API B.hom.fiber.
- def-sbc-smooth-morphisms: Mathlib.AlgebraicGeometry.Morphisms.Smooth,
  AlgebraicGeometry.Smooth (the affine-local smooth-ring-map definition).
- def-weil-proper-morphism: Mathlib.AlgebraicGeometry.Morphisms.Proper,
  AlgebraicGeometry.IsProper, IsSeparated and UniversallyClosed.
- def-weil-closed-immersion:
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion,
  AlgebraicGeometry.IsClosedImmersion.

Additional existing component APIs, without redefining any notion:
Mathlib.CategoryTheory.Monoidal.Cartesian.Grp exposes CategoryTheory.GrpObj and
IsCommMonObj; Mathlib.RingTheory.DedekindDomain.Basic provides IsDedekindDomain;
Mathlib.RingTheory.KrullDimension.Basic provides ringKrullDim. Their defining
signatures and docstrings were read. The node itself defines group scheme over
T, so no field-only group-scheme definition node is incorrectly specialized.

Proof-only imports retain the available plan:
WeilConjectures.AlgebraicGeometry.Morphisms.GenericFibreCoverDensity
(Scheme.genericFibre_cover_reduced_and_dominant),
Mathlib.AlgebraicGeometry.Morphisms.Separated
(ext_of_isDominant_of_isSeparated), and Mathlib.AlgebraicGeometry.Gluing
(Scheme.Cover.glueMorphisms). The two proof dependencies
lem-sfb-proper-generic-map-big-open and
lem-sfb-relative-weil-codimension-extension currently have no Lean record or
mathlib_match, so have no module to import. They are proof dependencies only;
their declarations are not needed to type this stage-2 statement.

Edge cases checked: empty X gives the unique map on both sides; disconnected
and non-quasi-compact smooth X are admitted; the identity group scheme B = T
is admitted; no relative dimension or characteristic is restricted; T may be
the entire spectrum or any nonempty open, including a one-point generic open
when it exists. A field D is excluded precisely by the node's dimension-one
convention. A field E and schemes in a common arbitrary universe u do not
introduce a smaller independent test-object universe. No new mathematical
hypothesis is used to select the generic morphism.

Searches before writing (2026-10-24):

- msearch.py leanfinder: "An abelian scheme over a Dedekind domain has bijective
  restriction of morphisms from smooth schemes to the generic fibre". Eight
  hits, including smoothness and SpecToEquivOfField, but no Néron property.
- msearch.py leansearch: "An abelian scheme over a Dedekind domain has the Neron
  mapping property for arbitrary smooth schemes". Eight hits about smoothness,
  normalization and spectra; no extension theorem of this statement.
- msearch.py loogle: '"IsProper", "IsSmooth"'. Zero hits.
- msearch.py grep: Neron|Néron|[Aa]belian[Ss]cheme. Zero Mathlib hits.
- rg in lean/WeilConjectures and lean/Sheaf for Neron, Néron and abelian schemes:
  only unrelated derived Mayer-Vietoris text and the normal-semiabelian
  homomorphism extension / torsion-density modules. The former is for group
  homomorphisms between two semiabelian schemes over normal bases, not
  arbitrary smooth sources and arbitrary generic scheme morphisms.
- rg for the item id in lean/WeilConjectures and the Néron names in
  dag/lean_names_upstream.json: no match. Searches for GrpObj, IsCommMonObj,
  IsDedekindDomain and fibre APIs located the existing component definitions
  listed above. No duplicate definition is introduced.

The prescribed scompile.py compiled the delivered module in sandbox mode
(12.3 s) and at its library module path (7.0 s), without errors or unexpected
warnings. No statement correction or STATEMENT-DISPUTED fault was found.

## Second reading by Q103

A second pass by this same dispatcher-started worker compared the node and the
written module; no independent worker is claimed or started. The maintainer's
independent review remains the independent reading. The explicit dimension-one
binder was checked against Mathlib's dimension-at-most-one Dedekind convention.
ConnectedSpace is applied to the scheme-theoretic fibres rather than geometric
fibres or an unrelated topological predicate. The Hom domain is in Over T,
not Grp (Over T), and the codomain is in Over (Spec E). The restriction is the
existing functorial pullback of that exact map after forgetting the intermediate
open base, which is canonically the node's generic restriction by pullback
pasting. Nonempty is on T only, and no quasi-compactness condition occurs on X.
All proof-plan paragraphs agree with the four DAG steps. No mismatch required
changing the node's statement, dependency list or proof.
