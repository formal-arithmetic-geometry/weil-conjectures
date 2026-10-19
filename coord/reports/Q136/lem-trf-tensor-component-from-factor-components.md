## Worker report

The module Sheaf.RingTheory.TensorComponentFromFactorComponents states
AlgebraicGeometry.tensor_component_from_factor_components, with one sorry and no new
definitions. It formalizes the component reduction of Stacks Algebra Tag 00EG. I read
literature/stacks-project/algebra.tex, lemma-connected-component and its proof, as well as
the item's seven proof steps. The docstring carries all seven steps and their inputs.

Hypotheses and clauses, in order:

- A commutative ring A and two commutative A-algebras are the three Type binders, three
  CommRing binders and two Algebra binders. Independent explicit universes u, v, w do not
  restrict the sizes of the algebras to the size of the base.
- A connected component Z is represented by connectedComponent z for a point
  z : PrimeSpectrum (B₁ ⊗[A] B₂). Every component has a point, so this is equivalent to
  quantification over components, including spectra whose components are not open.
- The component ideal is exactly the landed AlgebraicGeometry.componentIdeal: the ideal
  span of idempotents belonging to every prime in connectedComponent z. Membership in
  each prime is the condition Z ⊆ V(e). It is not the larger radical ideal of all functions
  vanishing on Z.
- D₁, D₂ and C are written as B₁ ⧸ componentIdeal B₁ z₁, B₂ ⧸ componentIdeal B₂ z₂ and
  (B₁ ⊗[A] B₂) ⧸ componentIdeal (B₁ ⊗[A] B₂) z. These are definitionally the existing
  componentRing. Quotient spelling exposes Mathlib's quotient Algebra instances; the
  componentRing wrapper only has a registered CommRing instance. No alternate definition
  or new instance is introduced.
- The existential points z₁ and z₂ specify the two components. The two image-subset
  conjuncts use PrimeSpectrum.comap of Algebra.TensorProduct.includeLeft/includeRight,
  precisely the maps underlying the two spectrum projections. They assert that the image
  of the entire component Z, rather than just its chosen point, is in each component.
- E is the tensor product of those two explicit quotients. The canonical map q is
  Algebra.TensorProduct.map of Ideal.Quotient.mkₐ A on the two component ideals. The first
  Function.Surjective asserts that this canonical map is a surjection.
- The existential A-algebra homomorphism r : E →ₐ[A] C has Function.Surjective r and
  r.comp q = Ideal.Quotient.mkₐ A (componentIdeal (B₁ ⊗[A] B₂) z). This is the asserted
  factorization of the canonical quotient p. Since q is surjective, this determines r.
- The point y of Spec E specifies its component W. The equivalence e : E/I_W ≃ₐ[A] C and
  e.toAlgHom.comp (Ideal.Quotient.mkₐ A I_W) = r identify C with that component ring over E.
- Compatibility with D₁ and D₂ follows by composing this last equality with their
  canonical tensor inclusions. Compatibility with B₁ and B₂ follows further by composing
  with their quotient maps and using r.comp q = p: these composites are exactly
  p.comp includeLeft and p.comp includeRight. Thus the single equality over E specifies
  both factor compatibilities, without allowing an arbitrary abstract ring isomorphism.

Dependency declarations read and used:

- def-weil-affine-spectrum: Mathlib.AlgebraicGeometry.Scheme,
  AlgebraicGeometry.Spec and Spec.map; their underlying point space and map are
  PrimeSpectrum and PrimeSpectrum.comap, used in the statement.
- lem-weil-pbc-algebra-tensor-pushout-universal-property (Mathlib leaf, no lean record):
  Mathlib.RingTheory.TensorProduct.Basic, Algebra.TensorProduct.instCommRing,
  tmul_mul_tmul, includeLeft, includeRight, ext; and
  Mathlib.RingTheory.TensorProduct.Maps, Algebra.TensorProduct.productMap and
  productMap_apply_tmul. I opened their signatures and docstrings. The module uses the
  same tensor structure and inclusions and the Maps declaration Algebra.TensorProduct.map
  for the canonical quotient map.
- Added the already landed statement dependency
  lem-trf-affine-etale-cover-component-criterion, module
  Sheaf.TraceFormula.AffineEtaleCoverComponentCriterion, whose recorded declarations
  include componentIdeal, componentRing, componentRing.instCommRing and componentSpectrumMap.
  I read that module and the node. The first conjunct of affineEtaleCover_componentCriterion
  identifies Spec(T/I_Z) with connectedComponent z. This is a use of the existing
  component-ring construction, not a new node or dependency repair.
- Proof inputs are available through Mathlib's prime-spectrum topology and quotient
  declarations (compactSpace, iSup_basicOpen_eq_top_iff,
  existsUnique_idempotent_basicOpen_eq_of_isClopen, isIdempotentElemEquivClopens,
  isClosedEmbedding_comap_of_surjective, range_comap_of_surjective), the direct proof import
  Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated (quasiSeparatedSpace_iff_forall_affineOpens,
  Scheme.quasiSeparatedSpace_of_isOpenCover), and
  WeilConjectures.Topology.SpectralSpace.ConnectedComponent
  (sInter_isClopen_and_mem_eq_connectedComponent). I read their full declarations and the
  proof-dependency node records. No proof dependency with a separate available project
  module has been omitted.

Edge cases checked: if the tensor product is the zero ring, it has no prime point z, so
there is no spurious nonempty-component hypothesis. A zero factor has the same consequence.
No reducedness, Noetherianity, local connectedness, flatness, finite generation, nonzero-ring
assumption or openness of components is used. For connected spectra of the factors the
same formulation applies without a clopen decomposition. Infinitely many non-open components
are allowed. Nonreduced rings retain their nilpotents: the quotient uses the ideal generated
by idempotents, rather than all functions vanishing on the component. The final equality
prevents an abstract quotient equivalence that does not respect the factor maps.

Searches (msearch.py, group Q136, this item):

- LeanFinder: "A connected component of the spectrum of a tensor product is a component ring
  of the tensor product of component quotient rings of its factors". Eight hits, including
  PrimeSpectrum.tensorProductTo, continuous_tensorProductTo, embedding lemmas with extra
  surjective-on-stalks assumptions, and a purely inseparable spectrum homeomorphism. No
  theorem supplies the component quotient and compatible factorization.
- Loogle: '"connectedComponent", "TensorProduct"'. Zero hits.
- LeanSearch: "A connected component quotient of a tensor product factors through the tensor
  product of the component quotients of the factors". Eight hits on module tensor-quotient
  equivalences, tensorQuotientEquiv, quotientTensorEquiv and Ideal.pi_mkQ_rTensor. None is a
  component-ring identification.
- msearch grep in Mathlib/RingTheory:
  connectedComponent.*tensor|tensor.*connectedComponent|componentRing|componentIdeal.
  Zero hits. Additional direct source reads located TensorProduct.map and Ideal.Quotient.mkₐ.
- rg in /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the same patterns and for this
  item's exact id: no existing component-ring reduction. rg of dag/lean_names_upstream.json
  for componentRing/componentIdeal: no match.
- rg of lean/Sheaf found the already landed componentIdeal/componentRing in
  TraceFormula/AffineEtaleCoverComponentCriterion.lean, which are reused. The other tensor
  and component matches, including ArtinTensorEtaleAcyclic, do not state this reduction.

No statement correction, disputed statement, new node or dependency module is needed.
The only DAG delta outside lean is the permitted addition of the landed dependency that
owns the existing component-ring definitions.

## Second reading by Q136

Author's separate self-check with the node and final file open; independent review is by
the maintainer, as prescribed in the dispatcher brief. I compared every clause again:
all three rings and both algebra structures are bound; z ranges over all components through
points; both projected sets are whole connected components' images; q is the tensor of the
two specified quotient maps and is surjective; r is a surjective A-algebra map with r q = p;
the last equivalence is from the exact idempotent component quotient of E and commutes with
its quotient map. Composing that equality gives the D_j compatibilities, and composing the
factorization gives the B_j compatibilities. There are no added finiteness or flatness
hypotheses and no lost empty-spectrum case. The only elaboration repair was spelling the
already defined componentRing as its defining quotient to obtain the existing quotient
Algebra instances. The natural statement is unchanged. The seven-step proof docstring
matches the node, including the kernel equality and avoiding unsupported idempotent lifting.
