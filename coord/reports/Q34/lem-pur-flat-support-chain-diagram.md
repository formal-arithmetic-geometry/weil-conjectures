## Worker report

This delivery states `AlgebraicGeometry.Etale.flatSupportChainDiagram` on ordinary
constant-A module sheaves on the small etale site, with actual integer cochain maps.
It defines the canonical tensor comparison, the displayed transpose h, its adjunct v,
and the functorial kernel map. All definition data are real constructions from the
existing monoidal comparison, ordinary adjunction and kernel universal property.
The only postponed proof is the main theorem; its docstring gives all seven proof
steps of the node. The node statement is unchanged.

Hypotheses and objects:

- Schemes U and P and their morphism j are the explicit `Scheme.{u}` and `U ⟶ P`
  binders. `[IsOpenImmersion j]` is precisely the open-immersion hypothesis.
- `A : Type (u + 1)`, `[CommRing A]`, `[Finite A]` give the finite commutative ring,
  including the zero ring. The module and site size convention is that of the
  recorded `DerivedCategoryModule`: `Sheaf P.smallEtaleTopology (ModuleCat A)`.
- Q, I and J are arbitrary `CochainComplex ... ℤ`, with no boundedness restriction.
  `_hQ : ∀ p, exactFunctor _ _ (tensorRight (Q.X p))` says precisely that tensoring
  with each term of Q is exact. This uses the `exactFunctor` recorded with
  def-pc-flat-sheaf-modules, with the fixed ordinary constant-coefficient encoding
  from def-weil-pbc-derived-categories. It does not assert K-flatness.
- `a : Q ⊗ I ⟶ J` is any A-linear chain map. The monoidal cochain tensor is the
  direct-sum `mapBifunctor` tensor from def-pc-tensor-complex-sheaves, with its
  standard signed differential.

The actual support row is `OpenSupport.row adj I`, the Mathlib `kernelSequence`
of the termwise adjunction unit. This is definitionally the upstream
`supportsShortComplex (ModuleCat A) j I`:
its X₁ is `kernel (supportsUnit ... I)`, its f is the kernel inclusion, X₂ is I,
its g is the termwise adjunction unit r_I, and X₃ is j_*j^*I. The J row is identical
with J substituted. `OpenSupport.restriction` is the termwise unit.
`OpenSupport.kernelMap` is the standard `kernel.map` of unit naturality.
`OpenSupport.Diagram` bundles precisely the five conclusion clauses below; the
main theorem applies it to `upperStarLowerStarAdjunction (ModuleCat A) j`.
It introduces no independent mathematical notion or arbitrary adjunction.
All generic-helper universes are explicit; their extra structures are inferred
from the concrete etale module-sheaf categories in the main theorem. The source declaration and full definitions were read in
`WeilConjectures.SixFunctors.OpenClosed.Supports`, not inferred from the name.

Conclusions:

- `OpenSupport.comparison` is c_{Q,K}, obtained by totaling the existing
  canonical ordinary oplax tensor comparison; the inverse is its `asIso` inverse.
  The generic helper shares the monoidal structures during elaboration; it adds
  no choice of a comparison or additional assumption to the etale theorem.
- `OpenSupport.transpose` composes c_{Q,C}, the tensor of the identity and
  the ordinary termwise counit, c_{Q,I}^{-1}, and j^*a, in that order in Lean's
  left-to-right composition convention. This is exactly the displayed h.
- `OpenSupport.rightMap` is the termwise unit followed by j_* of that transpose,
  exactly the displayed v. Its type is a chain-map type, so being a chain map is
  part of the construction, without an extra proposition or hypothesis.
- The first conjunction is `(Q ◁ r_I) ≫ v = a ≫ r_J`, the right-hand square.
- The next conjunction quantifies over all p,q,n and p+q=n; after the total
  summand inclusion it identifies v^n with the ordinary adjunction `homEquiv`
  applied to the ordinary tensor comparison, counit, inverse comparison, and
  j^* of the summand of a. No preservation of sums by j_* is imposed.
- `∃! u, u ≫ s_J = (Q ◁ s_I) ≫ a` is exactly existence and uniqueness of the
  left-hand chain map. Together with the first square it is the strict row diagram.
- Only in the short-exactness implication are the degreewise epi hypotheses on
  r_I and r_J assumed. The conclusions are `.ShortExact` for both rows after
  evaluation in each n; the top row first uses `.map (tensorLeft Q)`.
- The final universal quantifiers give arbitrary I',J',a',f,g and the specified
  compatibility `a ≫ g = (Q ◁ f) ≫ a'`. The right quotient square and the kernel
  square are stated as equations of chain maps; the middle square is the given
  compatibility. All first maps satisfying the kernel characterization are covered,
  so this states naturality of the uniquely induced map, without epi hypotheses.

Dependency declarations read and used:

- def-weil-pbc-scheme-conventions fixes no declaration; `Scheme` and
  `IsOpenImmersion` are the specified Mathlib notions.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule` and its ordinary module-sheaf
  category convention. No derived quotient is taken in this item.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`, the exact ordinary adjunction
  and constant-ring module-pullback interpretation.
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`:
  `CategoryTheory.Adjunction.mapHomologicalComplex` (part (a) of the recorded
  termwise adjunction node; its homotopy-category extension is not substituted).
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite` and `CategoryTheory.exactFunctor`, exact tensor
  functor flatness. The latter is applied directly to the fixed-constant sheaf
  tensor; no second flatness predicate is introduced.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`, with
  the monoidal realization and summand inclusions supplied by
  `WeilConjectures.Mathlib.Algebra.Homology.Monoidal`.
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`:
  `CategoryTheory.CochainPullback.cochainPullbackTensorCoherence`; its signed
  cochain comparison is specialized to ordinary constant-coefficient inverse image
  by the canonical monoidal `upperStar` interface in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal`.
- Proof-only imports: `Sheaf.CategoryTheory.RingedSiteModules` and its
  `CategoryTheory.ringedSiteModules`, and
  `WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian` with
  `AlgebraicGeometry.Scheme.etaleModuleSheaves_grothendieckAbelian` (all colimits
  and exact filtered colimits). Their full docstrings and signatures were read.

Edge cases checked mathematically before completing the statement: Q=0, I=0 and
J=0; the zero coefficient ring; the empty scheme; j the empty open (unit targets
zero and the kernels are the original complexes); j the identity (kernel zero);
arbitrary unbounded complexes and the countably infinite diagonal p+q=n; and
units which are not degreewise epi. No clause asserts surjectivity on sections
from a sheaf epimorphism. The epi assumptions are confined to short exactness.
No second coefficient ring or action occurs.

Source read: sites-cohomology.tex, `lemma-restriction-along-monomorphism-surjective`
(Tag 093X) and `lemma-pullback-tensor-product` (07A4); sites-modules.tex,
`lemma-abelian` (03DA), `lemma-limits-colimits` (03DB), and `definition-flat` item
(3) (03ER). The node explicitly calls its refinement agent-written: 093X alone
is not claimed to state this stronger cochain diagram.

Searches actually run through msearch.py (logged in searches.jsonl):

- LeanFinder, “Flat term tensor of sheaf cochain complexes and open adjunction
  induce a natural strict kernel support diagram”: eight hits, including sheaf
  cohomology and Mayer–Vietoris short complexes; none states this diagram.
- Loogle, `CategoryTheory.ShortComplex, CochainComplex`: twelve hits, principally
  degreewise-split triangles and mapping cones; no match for this statement.
- Mathlib grep, `support.*[Tt]ensor|[Tt]ensor.*[Ss]hort[Ee]xact`: one hit,
  `Module.mem_support_iff_nontrivial_residueField_tensorProduct`, not a match.
- The existing logged LeanSearch query “An open immersion of etale topoi and a
  tensor chain map induce a natural commuting diagram of kernel support sequences”
  found eight open-immersion declarations, none this statement.
- rg over both WeilConjectures and Sheaf for the node id, FlatSupport, and
  SupportChainDiagram found the larger K-flat-support comparison and its data.
  Reading both modules showed stricter hypotheses and a derived comparison,
  rather than this arbitrary-chain-map statement. The existing support rows,
  monoidal comparison and adjunction were reused.

No statement dispute, new independent notion, or dependency replacement is needed.

Validation: scompile.py compiles the complete file in both sandbox and library
contexts with no errors or warnings (5.8 s and 5.4 s). The generic helper avoids
repeated unfolding of specialized sheaf monoidal structures. No timeout limit
was raised. Every definition has real data, and only the main theorem has sorry.

## Second reading by Q34

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
