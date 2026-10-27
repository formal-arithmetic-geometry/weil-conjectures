## Worker report

Item: lem-sfb-space-affine-etale-polynomial-generators. Module:
`Sheaf.AlgebraicGeometry.AffineEtalePolynomialGenerators`. Main declaration:
`AlgebraicGeometry.AlgebraicSpace.affine_etale_polynomial_generators`.
Only that theorem is postponed, with `sorry`; its docstring contains the complete
seven-step DAG proof. There are no postponed data definitions or auxiliary theorems.

The output is packaged as `Nonempty (PolynomialAtlasPresentation U p)`. This is a
witness of exactly the conclusion, not an extra input hypothesis. The structure
records the actual algebra map and its normalization, not merely a module epimorphism.
Its polynomial object is characterized by the monomial coproduct universal property.
This determines the free commutative algebra up to the unique isomorphism preserving
the specified global variables: each monomial inclusion is multiplication by that
monomial; the coproduct property determines every linear map out of it, and the
monomial multiplication formula makes evaluation multiplicative. This formulation
does not assert that polynomial sections on an arbitrary test object are globally
finite polynomials; sheaf coproducts permit locally finite expressions.

Hypotheses and clauses, in order:

- An arbitrary scheme S and an algebraic space over S are the explicit binders
  `{S : Scheme.{u}} (X : AlgebraicSpace S)`. No restriction on S is imposed.
- Regarding X over Spec Z is `absoluteBaseChangeToIntegers X`. This uses the landed
  `exists_spaceChangeBase (specULiftZIsTerminal.from S)` from Tag 04SG. The selected
  extension is characterized on sections by the sigma formula, restrictions, action
  on arrows and its projection to S, so selection is by a normalized universal
  construction. The same theorem identifies every original scheme chart, covering,
  and regular-function ring with those of the extended space. It supplies exactly
  the small etale ringed-site identification stipulated by the node. ULift Z keeps
  the base in universe u without changing the mathematical base.
- V is `(V : Scheme.{u}) [IsAffine V]`. The morphism f has target the representable
  space of V over Spec Z. In particular f is an absolute morphism; V is not required
  to have an S-structure or a finite-type property.
- Its diagonal is closed on scheme tests exactly by `hf : IsRepresentableWith
  (fun _ _ a ↦ IsClosedImmersion a.left) (Limits.pullback.diagonal f.hom.hom)`.
  This reuses both the dependency's representable-property interface and Mathlib's
  closed immersion and fibre product, rather than introducing separatedness anew.
- The affine chart is `(U : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
  [IsAffine U.left]`. Writing an arbitrary affine U with its canonical ring
  `B = Scheme.Γ.obj (op U.left)` is equivalent to the node's U = Spec B, via the
  affine scheme's canonical Spec-of-global-functions isomorphism. This retains
  the given chart, without choosing a different cover or adding a B-structure.
- `p : schemeSpace U ⟶ absoluteBaseChangeToIntegers X`, `hp : IsEtale p.hom.hom`
  and `hs : IsSurjective p.hom.hom` give exactly the representable surjective etale
  chart. Both predicates include representability on all scheme tests.
- The direct image is exactly `(moduleDirectImage p).obj
  (SheafOfModules.unit (schemeSpace U).structureSheaf)`. The witness's
  `quasiCoherent` field asserts its Mathlib `IsQuasicoherent` predicate.
- The witness's `F : X.CommAlgebraSheaf` retains its underlying module via
  `underlying`. Its `projection` and `projection_eq` fields make every projection
  of the specified module direct-image model a ring homomorphism. These conditions
  fix the componentwise multiplication and unit. Linearity and unitality also fix
  the coefficient map. No arbitrary algebra structure on an abstract module is used.
- `globals` is a bijection B with the global sections of that same algebra module.
  `globals_eq` fixes it on every chart: b goes to pullback of b along the actual
  scheme map from that chart to U. The chart-limit property makes these identities
  a unique identification, and componentwise ring operations make it the ring
  identification B = Gamma(X,p_*O_U) stipulated by the node.
- `m : ℕ` and `g : Fin m → Scheme.Γ.obj (op U.left)` are precisely the finite list
  of generators, with m = 0 permitted.
- `P : X.CommAlgebraSheaf`, its global variables `z`, its maps `monomial`, and
  `monomial_eq` specify the ordinary monomials in those variables, including the
  constant monomial d = 0. `monomial_isColimit : IsColimit (Cofan.mk P.toModule
  monomial)` is exactly the stated module coproduct, one copy of O_X per monomial.
  Together with the algebra operations this is the free polynomial algebra, not an
  arbitrary algebra equipped with a possibly non-surjective list of variables.
- `evaluation : P ⟶ F` is a morphism in the under-category of the structure
  commutative-ring sheaf, hence a morphism of O_X-algebra sheaves. Its module map
  `evaluationModule` agrees on every local section by `evaluationModule_eq`.
  `evaluation_z` says exactly z_i maps to the global section corresponding to g_i.
  The monomial coproduct property then uniquely determines evaluation on all sections.
- `surjective` is `Presheaf.IsLocallySurjective X.etaleTopology
  evaluation.right.hom`, the node's surjectivity as sheaves (local lifts), rather
  than an unjustified assertion of sectionwise surjectivity on every test object.
- `kernel_quasiCoherent` is the Mathlib quasi-coherence of
  `kernel (evaluationModule ≫ underlying.hom)`. Thus the kernel is taken as a
  module sheaf into the specified canonical module direct image, as requested.
- There is no cohomology, finite-type, Noetherian, quasi-compactness-of-f, or extra
  separation hypothesis. Quasi-coherence of the polynomial source is a consequence
  of its displayed coproduct, not an added input.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`,
  `IsEtale`, `IsSurjective`, `EtaleSite`, `etaleForget`, `structureSheaf`, `Modules`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `Limits.pullback`
  and its diagonal (via the imported site and scheme interfaces).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `ModuleDirectImageModel`, `ModuleChart`, `moduleDirectImageModel`, `moduleDirectImage`;
  the existing chart-limit projections are used verbatim.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`'s underlying
  predicate `SheafOfModules.IsQuasicoherent` and its small-etale slice instances.
- Added the already landed statement dependency `lem-sfb-space-change-base-to-integers`:
  `Sheaf.AlgebraicGeometry.SpaceChangeBase`, `exists_spaceChangeBase`. This is the
  exact normalized sigma extension and small-etale ringed-site equivalence, not a
  replacement interface.
- Added the already landed statement dependency `def-sfb-space-quasi-coherent-algebra`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentAlgebra`, `commStructureSheaf`,
  `CommAlgebraSheaf`, `CommAlgebraSheaf.toModule`. The algebra notion is reused.
- Stated proof dependencies have plain imports: the quasi-coherent pushforward,
  etale pushforward restriction, etale fibre products, and chartwise permanence
  modules. The remaining project proof dependencies have no landed Lean module;
  their DAG proof references are retained in the main theorem's docstring. Mathlib
  proof inputs include affine scheme fibre products, etale finite presentation and
  open-immersion etaleness.

Sources read: spaces-cohomology.tex, proposition-vanishing-affine (Tag 07V6), proof
from the choice of U through local surjectivity, before the H1 argument;
spaces-properties.tex, lemma-properties-quasi-coherent (Tag 03M1), direct sums and
kernels. The recorded Tag 04SG dependency module was read in full, including its
sigma normalization and small-etale ringed-site equivalence.

Edge cases checked before finalizing:

- m = 0: Fin 0 is empty but the zero exponent vector still indexes the constant
  monomial; its product is 1. Thus P is O_X, rather than the zero module.
- Zero chart ring and empty schemes/spaces: no Nontrivial or Nonempty hypotheses
  occur; the globals equivalence, ring homomorphisms and monomial coproduct make
  sense also in the zero category.
- Arbitrary nonempty or empty test schemes, and disconnected/non-quasi-compact
  test objects: only local surjectivity is claimed. Polynomial sections are governed
  by a sheaf coproduct; no globally bounded finite-expression assumption is made.
- Arbitrary base S and affine V, with no map V to S: the morphism is typed over
  Spec Z, so nonseparated and non-finite-type bases are not silently excluded.
- Section carriers are in universe u, with the site in u+1; u is explicitly bound.
  No extra equality of site and section universes or universe of test rings is imposed.

Searches for existing statements/notions:

- msearch.py leanfinder, query "An affine etale chart of a separated algebraic space
  has direct image structure algebra generated by finitely many global sections":
  8 hits, including StandardEtalePresentation, Algebra.Etale.finitePresentation,
  Algebra.Etale.exists_subalgebra_fg and scheme etale declarations; none states
  the algebraic-space direct-image polynomial-generator assertion.
- msearch.py loogle, query "MvPolynomial, SheafOfModules": OK, 0 hits.
- msearch.py leansearch, query "free polynomial algebra sheaf global variables
  monomial coproduct": 8 hits, notably SheafOfModules.free, ιFree, freeCofan,
  isColimitFreeCofan and MvPolynomial.instFree. These support the monomial
  characterization; they do not state this item's result.
- msearch.py grep, query "polynomial|Polynomial" in Algebra/Category/: 18 hits,
  ring polynomial functors and finite-type commutative algebra presentations,
  with no matching algebraic-space assertion.
- rg of polynomial/sheaf terms in lean/Sheaf, lean/WeilConjectures and dag/nodes
  found SheafPolynomialCotangent.polynomialSheaf. Its source was read: it is
  a construction for a small category C : Type u with section rings in Type u,
  rather than this large small-etale site (objects u+1, sections u). This delivery
  neither copies that construction nor identifies raw polynomial presheaves with
  sheaves: it states the existence of the polynomial sheaf by the same free
  universal property, expanded as the monomial coproduct explicitly requested here.
- Exact proposed names searched by rg in Mathlib, WeilConjectures, Sheaf and
  dag/lean_names_upstream.json: no collisions. rg/grep for the item id in
  WeilConjectures found no existing declaration.
- The prescribed CompactObject example is now a withdrawn module with no
  declarations. Its node and the active neighboring module headers were read;
  this delivery follows the current module/public-import/expose conventions.

Validation: scompile.py compiled both its private sandbox module and the final
library-path module cleanly, 13.5 seconds each. Every delivered Lean declaration
has source and blueprint docstrings; all lines have at most 100 characters.
No statement correction, new independent notion, or dependency repair was needed.
Only `lean` and the addition of the two landed statement dependencies change in
the item's node copy. No live source or Git command was used directly.

## Second reading by NC

The dispatcher expressly prohibits starting other agents and assigns independent
review to the maintainer. This section records the worker's explicit self-check,
not an independently authored review. Re-read the node, the complete Lean file,
and both source excerpts after the clean compile. Checked each hypothesis and
clause against the mapping above, especially the absolute morphism over Spec Z,
canonical chart-projection normalization, m = 0, monomial coproduct universal
property, genuine algebra-map evaluation, local surjectivity, and the kernel in
the specified module direct image. The implementation has no claimed independent
second reading before delivery; that review remains the maintainer's.
