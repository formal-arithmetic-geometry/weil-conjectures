## Worker report

The module `Sheaf.TraceFormula.GeometricallyIntegralFibresLimitDescent` states
`AlgebraicGeometry.exists_eventually_geometricallyIntegral_fibres`, with proof `sorry`.
It changes only the item's `lean` field. No definitions, new nodes, dependency repairs,
or statement corrections are needed. No statement dispute was found.

The source is `literature/stacks-project/more-morphisms.tex`, proofs of Tags 05FG and
05FH, read together with `literature/stacks-project/limits.tex`, Tag 05F4. The argument
uses the intersection of the reduced and irreducible constructible loci for the fixed
finite-presentation model; the source's mechanism applies to the given arbitrary directed
ring system. The declaration docstring records all six proof steps and their DAG nodes.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Small nonempty directed set I | `{I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]`; this is the project's directed-set convention, allowing preorders. |
| Directed system of commutative rings and compatible unital transition maps | `D : I ⥤ CommRingCat.{u}`; the preorder category gives transitions, ring-category morphisms are unital ring maps, and functor laws encode identities and composition. |
| Specified colimit A with its compatible maps | `c : Cocone D`, `hc : IsColimit c`; A is `c.pt`, and the specified maps are `c.ι.app j`. This uses the dependency's universal-property formulation and does not assume injectivity. |
| Fixed a in I | `(a : I)`. |
| Finitely presented A_a-algebra C_a | `(C : Type u) [CommRing C] [Algebra (D.obj a) C] [Algebra.FinitePresentation (D.obj a) C]`. |
| C = C_a tensor A over A_a, with its canonical A structure | `c.pt ⊗[D.obj a] C`, using the algebra structure `(c.ι.app a).hom.toAlgebra`, installed by the first explicitly applied `id`. The order is reversed by the canonical `Algebra.TensorProduct.comm`; the new base is first, so Mathlib's global `leftAlgebra` supplies exactly the desired base algebra. |
| For every prime p of A | `∀ p : PrimeSpectrum c.pt` inside `hgeom`. |
| Fibre C tensor_A κ(p) | `p.asIdeal.Fiber (c.pt ⊗[D.obj a] C)`, definitionally κ(p) tensor_A C; tensor symmetry gives the node's order. |
| Geometric integrality of the fibre over κ(p) | `GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber ...))))`. This is the dependency's exact Mathlib class for the spectrum's structure map to Spec κ(p). |
| There is b at least a | `∃ b : I, ∃ hab : a ≤ b`. |
| For every j at least b | `∀ (j : I) (hbj : b ≤ j)`; equality j = b is included. |
| C_j = C_a tensor A_j over A_a, with the specified transition action | `D.obj j ⊗[D.obj a] C`, using `(D.map (homOfLE (hab.trans hbj))).hom.toAlgebra`, installed by the second applied `id`. No arbitrary action or an extra compatibility hypothesis is supplied. |
| For every prime q of A_j | `∀ q : PrimeSpectrum (D.obj j)`. |
| Geometric integrality of C_j tensor_{A_j} κ(q) over κ(q) | The same `GeometricallyIntegral (Spec.map (... algebraMap ...))` with `q.asIdeal.Fiber (D.obj j ⊗[D.obj a] C)`. |
| Spectrum nonempty, reduced and irreducible after every field extension | `GeometricallyIntegral` is `geometrically IsIntegral`; `geometrically_iff_of_commRing` gives every field extension, and `IsIntegral` is equivalent to `IrreducibleSpace ∧ IsReduced`. `IrreducibleSpace` includes nonemptiness. |
| No flatness, Noetherian or injectivity assumptions | No such binders occur; the only mathematical conditions are directedness, the actual ring colimit, finite presentation and the geometric-fibre hypothesis. |

All index, ring and tensor universes are explicit. The index and ring diagrams are in the
same universe as required by the project's colimit size convention; `autoImplicit` and
`relaxedAutoImplicit` are both false. The `id` applications are ordinary reduction of
explicit functions at canonical algebra structures, without hidden `let` or `show` binders.

Statement dependency declarations read and used:

- `def-weil-pbc-category-colimit`: `Mathlib.CategoryTheory.Limits.HasLimits`,
  `CategoryTheory.Limits.Cocone`, `CategoryTheory.Limits.IsColimit` and its universal
  property (rather than replacing the specified colimit by a chosen one).
- `def-weil-pbc-finitely-presented-algebra`: `Mathlib.RingTheory.FinitePresentation`,
  `Algebra.FinitePresentation`.
- `def-weil-module-base-change`: `Mathlib.LinearAlgebra.TensorProduct.Tower`,
  `TensorProduct`, with the canonical left module structure; `LinearMap.baseChange`
  is the recorded map form of the same notion, not needed as an additional map here.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField`. The ring residue field used in the statement
  is its standard affine model `Ideal.ResidueField`; `Spec.residueFieldIso` identifies
  these exactly. `Ideal.Fiber` in `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`
  is the existing residue-field tensor construction, also used by both recorded fibre loci.
- `def-pc-geometrically-irreducible`: `Mathlib.AlgebraicGeometry.Geometrically.Integral`,
  `AlgebraicGeometry.GeometricallyIntegral`. Its specialization to the fibre structure
  map is precisely the node's field-extension predicate, including nonemptiness.
- `lem-weil-pbc-algebra-tensor-pushout-universal-property` is a Mathlib leaf with no
  `lean` field: its `mathlib_match` points to `Mathlib.RingTheory.TensorProduct.Basic`
  and `.Maps`, `Algebra.TensorProduct.instCommRing`, `instAlgebra`, `includeLeft`,
  `includeRight`, `productMap`, `productMap_apply_tmul`, and `ext`. Their signatures
  and docstrings were read; the tensor and canonical algebra structures are used directly.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral`, with `isIntegral_iff_irreducibleSpace_and_isReduced`.

All stated proof dependencies are imported privately, using their recorded modules or
Mathlib matches. In particular these include
`WeilConjectures.Mathlib.FieldTheory.IsSepClosed`
(`IsSepClosure.exists_intermediateField_mem`),
`WeilConjectures.AlgebraicGeometry.SubsetGeometricIrreducibility`
(`isIrreducible_preimage_of_isSepClosed_extension`),
`WeilConjectures.AlgebraicGeometry.LimitContainedInConstructible`
(`exists_eventually_range_subset_of_isConstructible`),
`Sheaf.TraceFormula.GeometricFibreComponentCountBaseChange`
(`geometricFibreComponentCount_baseChange`),
`Sheaf.TraceFormula.GeometricallyIrreducibleFibreLocus`
(`geometricallyIrreducible_fibre_locus_constructible`), and
`Sheaf.AlgebraicGeometry.GeometricallyReducedFibreLocus`
(`geometricallyReduced_fibre_locus_constructible_baseChange`). The remaining Mathlib
proof imports supply `Topology.IsConstructible`, `irreducibleComponents` and its covering
lemmas, affine qcqs, `pullbackSpecIso`, and `Spec.reflective` respectively. There is no
import cycle omitted from the plan.

Edge cases checked before writing:

- If A is the zero ring, the prime quantifier in the hypothesis is empty. In a filtered
  colimit 1 = 0 is witnessed at a finite stage, so a cofinal tail consists of zero rings;
  the conclusion is also vacuous on prime spectra. No nontriviality assumption is added.
- If C_a is the zero algebra and A is nonzero, every fibre is the zero ring, with empty
  spectrum, so `hgeom` fails. If A is zero, the preceding case applies. Nonempty fibres
  are not silently replaced by preirreducibility.
- In a constant system the statement reduces to preservation under the canonical
  identifications and may take b = a. A one-element index type is allowed.
- A reduced reducible fibre does not satisfy `GeometricallyIntegral`; reducedness alone
  is insufficient. Nilpotent or geometrically nonreduced fibres are also excluded.
- No separability of residue-field extensions is imposed; the geometric-integrality
  class tests every extension, including inseparable ones.
- Transition maps may be noninjective, and primes need not lift from Spec A. The conclusion
  quantifies over all primes of every late A_j, not merely the image of the colimit spectrum.

Searches for an existing declaration (all msearch calls run for this group and item):

- LeanFinder, `Geometrically integral fibres of a finitely presented algebra descend along
  a directed colimit of base rings`: eight hits, principally
  `RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit`,
  `RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit`, base-change stability for
  finite presentation, and integral morphisms. None asserts this eventual geometric-fibre
  property. An earlier phrasing `eventually geometrically integral fibres directed colimit
  commutative rings` similarly returned integral-morphism and colimit construction facts.
- LeanSearch, the same full sentence: eight hits including
  `Ring.DirectLimit.commRing`, `Algebra.IsGeometricallyReduced.of_forall_fg`, and
  general descent/local-finite-type facts; none is the requested statement.
- Loogle, `AlgebraicGeometry.GeometricallyIntegral`: twelve hits including the class,
  base-change instances, and its reduced/irreducible decomposition. These provide the
  predicate, not the finite-stage reflection. The initial multi-name query with an
  unqualified class name returned no hits; it was rerun with the qualified name.
- msearch grep, `GeometricallyIntegral|geometricallyIntegral|geometrically_integral`
  in `AlgebraicGeometry`: nine hits in the geometric-integrality definition, abelian-group
  schemes, and affine space. No directed-limit statement. Earlier lowercase-only and
  malformed-subdirectory grep queries returned no hits and were replaced by this query.
- `rg` over the live project's `lean/WeilConjectures` and `lean/Sheaf` with the same
  predicate names and geometric-fibre/limit wording, and the exact item id: no existing
  statement for this node. The closest sibling is
  `Sheaf.TraceFormula.GeometricallyReducedFibresLimitDescent.exists_eventually_geometricallyReduced_fibres`
  (declaration namespace `AlgebraicGeometry`), which concerns only reducedness and allows
  empty fibres; it does not state geometric integrality. Neighbourhood and projectivity
  theorems with integral fibres also have different statements.
- The proposed declaration name was checked in Mathlib, both live project roots and
  `dag/lean_names_upstream.json`; no existing declaration with that name was found.

Validation: prescribed server `scompile.py` compiled the complete module in sandbox mode
and at its library module path, without errors or warnings (4.3 s and 1.8 s respectively).
The signature in `lean.statement` is extracted verbatim from the module. The JSON uses
indent 1, Unicode, and a final newline. No file outside this item's sandbox was edited.

## Second reading by Q44

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
