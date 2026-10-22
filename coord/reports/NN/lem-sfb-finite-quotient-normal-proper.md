## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteQuotientNormalProper` states
`AlgebraicGeometry.finiteQuotient_normal_proper`. Its sole theorem has proof `sorry`.
There are no new definitions, helper theorems, dependency repairs, or statement corrections.
The node copy differs from the current live node only in `lean`. In particular the
maintainer's Artin--Tate citation correction is preserved: the source, proof step 2,
proof dependencies, and Lean docstring cite
`lem-sfb-artin-tate-subalgebra-finite-type`, not the retired `lem-per-...` node.
The previous attempt's stale stage-1 split was not reused.

Source read: ILO, Travaux de Gabber, Expose X 2.3, Steps 2--3, printed pp. 151--152,
including diagram (2.c) and the component/stabilizer reduction. This node is explicitly
an agent-formulated prerequisite about an existing quotient, not the quotient existence
or projectivity theorem. Also read Stacks `algebra.tex`, lemma-Artin-Tate (00IS), and the
complete nine-step proof in the current node. Its source-specific hypotheses are all
represented below; the proof is recorded step by step in the theorem's docstring.

Hypothesis and conclusion correspondence:

- A field k: `(k : Type u) [Field k]`. The schemes `X Z : Scheme.{u}` have structure maps
  `a : X ⟶ Spec (CommRingCat.of k)` and `b : Z ⟶ Spec (CommRingCat.of k)`.
- X normal: `hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
  IsIntegrallyClosed (X.presheaf.stalk x)`. This is the node's normal-domain condition at
  every local ring, with neither global integrality nor connectedness imposed.
- X proper of finite type: `[IsProper a]`. Mathlib's properness includes
  `LocallyOfFiniteType a` and universal closedness, the latter implying `QuasiCompact a`.
  Thus the node's full finite-type condition is included without a redundant binder.
- A finite group acting on X over k: `(H : Type v) [Group H] [Finite H]`,
  `(α : H →* Aut X)`, and `hα : ∀ h, (α h).hom ≫ a = a`.
  Mathlib's automorphism multiplication agrees with composition of functions, so this is
  a left action; there is no faithful-action hypothesis.
- The supplied k-morphism q: `(q : X ⟶ Z)` and `hq : q ≫ b = a`.
- H-invariance of q: `hinv : ∀ h, (α h).hom ≫ q = q`.
- q finite and surjective: `[IsFinite q] [Surjective q]`, using the recorded Mathlib classes.
- Geometric fibres are H-orbits: `horbits` tests every algebraically closed field Ω of
  the schemes' universe and every pair `x y : Spec Ω ⟶ X`, asserting
  `x ≫ q = y ≫ q ↔ ∃ h, x ≫ (α h).hom = y`. For a finite morphism, points of the
  geometric fibre over Ω are exactly these Ω-valued lifts; finite algebras over an
  algebraically closed field have residue field Ω. Surjectivity and finiteness already
  supply a lift over each geometric point. This condition includes geometric points
  above arbitrary residue fields, not only k-rational or closed points.
- The canonical equality `O_Z = (q_* O_X)^H`: `hsections` asserts on EVERY open U of Z
  that the canonical pullback `q.app U` is injective and that a section s on the inverse
  image is in its image if and only if every h fixes s. The fixed-section formula is
  `(α h).hom.appLE (q ⁻¹ᵁ U) (q ⁻¹ᵁ U) e s = s` for every containment proof e.
  Invariance `hinv` gives `q ⁻¹ᵁ U = (α h).hom ⁻¹ᵁ (q ⁻¹ᵁ U)`, hence such an e
  always exists. Quantifying over e only avoids choosing an equality transport;
  by proof irrelevance all choices give the same ring map. This is exactly the
  automorphism pullback on the stable open, not a condition on global sections alone.
  Canonical pullback and its restriction naturality provide the sheaf identification.
- The categorical property is `hcategorical`: for every k-scheme `(W,c)` and k-morphism
  f (`f ≫ c = a`) invariant under every h, there exists a UNIQUE `g : Z ⟶ W` satisfying
  `g ≫ c = b ∧ q ≫ g = f`. Uniqueness is among k-morphisms, precisely as in the node.
- Z normal: the first conjunct quantifies over every z and gives both `IsDomain` and
  `IsIntegrallyClosed` of its local ring.
- Z proper: `IsProper b`.
- Z of finite type: `LocallyOfFiniteType b ∧ QuasiCompact b`, written explicitly.
- Z Noetherian: `IsNoetherian Z`. The class means locally Noetherian and quasi-compact.
  Mathlib `isNoetherian_iff_of_finite_iSup_eq_top` (Noetherian.lean:284) identifies this
  with the node's finite affine covering by spectra of Noetherian rings; the covering
  can be empty. This is the usual scheme condition, not a global-sections condition.
- No quotient existence, ample sheaf, projective embedding, or projectivity is asserted.
  The statement starts with Z and q already supplied and ends with only the four properties.

Dependency declarations used (the exact recorded interfaces were read):

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs, including nontriviality.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and its morphisms in
  Mathlib.AlgebraicGeometry.Scheme. Structure maps supply the schemes over k.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper` in
  Mathlib.AlgebraicGeometry.Morphisms.Proper, extending separatedness, universal
  closedness and local finite type. Properness supplies quasi-compactness.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` in
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType, and `AlgebraicGeometry.QuasiCompact`
  in Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- `def-weil-pbc-normal-ring`: the recorded inline conjunction of `IsDomain` and
  `IsIntegrallyClosed`, Mathlib.RingTheory.IntegralClosure.IntegrallyClosed, applied
  to the stalks. No second normal-ring predicate is introduced.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite`,
  Mathlib.AlgebraicGeometry.Morphisms.Finite.
- `def-weil-surjective-morphism`: `AlgebraicGeometry.Surjective`,
  Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  Mathlib.RingTheory.Noetherian.Defs, used through the standard Noetherian scheme class
  and its affine-chart characterization in Mathlib.AlgebraicGeometry.Noetherian.
- The action and geometric tests use existing `CategoryTheory.Aut` from
  Mathlib.CategoryTheory.Endomorphism and `IsAlgClosed` from
  Mathlib.FieldTheory.IsAlgClosed.Basic. The stable-open section map is existing
  `AlgebraicGeometry.Scheme.Hom.appLE`, Mathlib.AlgebraicGeometry.Scheme:196.

Proof-only imports retain the available interfaces of the plan:
`AlgebraicGeometry.Scheme.normal_sections_finite_product` from
WeilConjectures.AlgebraicGeometry.NormalSectionsFiniteProduct;
`Pi.isNormalRing_of_finite` from WeilConjectures.RingTheory.FiniteProductNormal;
`AlgebraicGeometry.isSeparated_of_surjective_universallyClosed` from
WeilConjectures.AlgebraicGeometry.IsSeparatedOfSurjectiveUniversallyClosed.
The Mathlib proof dependencies are available in the directly imported Noetherian,
FiniteType, Finite, Proper, UnderlyingMap, AffineScheme, UniversallyClosed, and
RingTheory.FiniteType modules. The corrected Artin--Tate node is still unsplit without
an attached Lean declaration, so it has no module to import at this stage. No proof
prerequisite has been duplicated or bypassed.

Edge cases checked:

- X empty: surjectivity forces Z empty. Normality has no points to check, the zero
  ring is permitted for sections, geometric-orbit tests have no lifts, and the empty
  affine cover is permitted by `IsNoetherian`. No `Nonempty X` or `Nonempty Z` occurs.
- Disconnected X and Z: normality is pointwise; neither `IsIntegral X` nor a global
  domain hypothesis occurs. The proof uses finite products and orbit stabilizers.
- Trivial and nonfaithful actions: α need not be injective. The identity quotient
  satisfies all quotient properties, and kernel elements simply act trivially.
- Characteristic dividing the group order: no invertibility or coprimality hypothesis
  occurs. The fixed-ring argument uses cancellation in a domain, not averaging.
- Arbitrary finite group universe v and scheme universe u are explicit. Geometric
  fields and test schemes use u, which contains all residue-field algebraic closures
  needed for these Scheme.{u} objects. Tests are not in a potentially smaller universe.
- The empty open U is included in hsections. The stable-open containment e cannot be
  vacuous, since its existence follows from hinv for every U and h.

Searches actually performed:

1. `msearch.py ... leanfinder`, query "An existing finite geometric quotient of a normal
   proper scheme over a field by a finite group is normal proper finite type and Noetherian".
   Eight hits: properness of finite morphisms, finite section rings, and abstract
   pre-Galois category decompositions. None states the existing quotient theorem.
2. `msearch.py ... leansearch`, query "A finite group quotient of a normal proper scheme
   over a field is normal and proper". Eight hits, comprising properness of finite
   morphisms and unrelated finite group quotient facts; no exact match.
3. `msearch.py ... loogle`, query
   "AlgebraicGeometry.IsProper, AlgebraicGeometry.IsNormal". Zero hits;
   `AlgebraicGeometry.IsNormal` is an unknown identifier. The node's recorded inline
   normality interface is therefore used.
4. `msearch.py ... grep`, query "quotient.*normal|normal.*quotient|GeometricQuotient"
   in AlgebraicGeometry. Zero hits.
5. `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for quotient/normal,
   invariant/proper, geometric-quotient, and finite-quotient spellings, together with
   the item's exact id and the proposed declaration name in `dag/lean_names_upstream.json`.
   Hits concern coefficient quotients, formal functions, or abstract group quotients;
   none provides this theorem or a scheme geometric-quotient interface to reuse.
   The proposed fully qualified declaration name is absent.

Validation: the delivered module was compiled with scompile.py against the current
published live library, both as a sandbox file and at its library module path. Both
passes were clean. No local/global Lake build was run. The theorem proof is solely
`sorry`; every universe and variable is explicitly bound.

No STATEMENT-DISPUTED issue or node fault was found. The previous blocker was an obsolete
stage-1 delivery; this packet is a Lean-only addition to the reviewed current DAG node.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
