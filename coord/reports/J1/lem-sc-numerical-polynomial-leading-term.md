## Worker report

The module `Sheaf.AlgebraicGeometry.NumericalPolynomialLeadingTerm` states
`AlgebraicGeometry.Scheme.Modules.numericalPolynomial_leadingTerm`, with proof `sorry`.
No theorem is proved. All three supporting definitions have complete data.
The item statement is unchanged; its stmt_deps gains the three definition nodes below.

Source read: Stacks Project [Tag 0BEN](https://stacks.math.columbia.edu/tag/0BEN),
Lemma 33.45.2, statement and entire devissage proof; also
[Section 0BEL](https://stacks.math.columbia.edu/tag/0BEL), including Lemma 33.45.1
and the integer-valued rational-polynomial interpretation in Lemma 33.45.4.
The local literature checkout contains only citation lists, so the source was read online.
The node writes the source's component Euler characteristic as the Euler characteristic
of its pushforward and twist on X. The delivered theorem follows that convention exactly.

Hypotheses and introduced objects, matched individually:

- Field k: `(k : Type u) [Field k]`.
- Proper k-scheme X: `(X : Scheme.{u}) [X.Over (Spec (.of k))]` and
  `[IsProper (X ↘ Spec (.of k))]`.
- Coherent O_X-module F: `(F : X.Modules)` and
  `(hF : RingedSpace.IsCoherent X.toRingedSpace F)`, using the recorded definition.
- Finite ordered family L_1,...,L_r: `(r : ℕ) (L : Fin r → X.Modules)` with
  `[∀ i, (L i).IsInvertible]`, using the recorded invertibility class.
- Support and its dimension: `(S : Set X) (hS : S = stalkSupport F)` and
  `(d : WithBot ℕ∞) (hd : d = topologicalKrullDim S)`. These equations introduce
  the objects named in the statement, with no restriction to nonempty support or natural d.
- The complete list of dimension-d irreducible components: `(s : ℕ)` and the
  equivalence `components : Fin s ≃ {C : Set S // C ∈ irreducibleComponents S ∧
  topologicalKrullDim C = d}`. Being an equivalence forbids omitted or repeated components.
  Components are subsets of the support with its subspace topology, as in the node.
- Their reduced integral closed-subscheme structures: `Z : Fin s → Scheme.{u}`,
  `[∀ i, IsIntegral (Z i)]`, `ι : ∀ i, Z i ⟶ X`, and
  `[∀ i, IsClosedImmersion (ι i)]`. `hι` identifies each range with the image in X
  of the corresponding component under `Subtype.val`. An integral closed subscheme
  with this range is precisely the reduced induced structure: reducedness comes from
  integrality, and a reduced closed-subscheme structure is determined by its underlying set.
- Generic points in X: `ξ : Fin s → X` and
  `hξ : ∀ i, IsGenericPoint (ξ i) (Set.range (ι i))`. This records the ambient
  points at which the local rings and F-stalks are evaluated.

Conclusions, matched individually:

- The numbers m_i are their local lengths and positive integers: `∃ m : Fin s → ℕ`
  with `∀ i, Module.length (X.presheaf.stalk (ξ i)) (F.presheaf.stalk (ξ i)) =
  (m i : ℕ∞) ∧ 0 < m i`. Equality to a natural number asserts finiteness as well
  as identifying each multiplicity; positivity is a separate clause.
- Every exponent n_i is an integer: the function passed to
  `IsNumericalPolynomialDegreeLT` has domain `Fin r → ℤ`. `multiTensorTwist`
  includes inverse powers through the dual and uses every factor in the given order.
- First term: `(multiTensorTwist F L n).eulerChar k`.
- Component term: `(pushforward (ι i)).obj (SheafOfModules.unit _)` is i_*O_Z,
  and its `multiTensorTwist` uses the very same L and n on X. The finite sum
  `∑ i : Fin s, (m i : ℤ) * ...` renders the exact weighted sum in the node.
- Difference is a numerical polynomial of total degree strictly less than d:
  `MvPolynomial.IsNumericalPolynomialDegreeLT ... d` means existence of a rational
  multivariate polynomial equal to this integer-valued function on every integer tuple,
  with sum of exponents of every nonzero monomial strictly less than d.
- When d=0 the strict bound forbids even a constant nonzero monomial; thus the
  polynomial is zero. This is encoded directly rather than using natural subtraction
  or the natural totalDegree of zero.

Dependency declarations read and used:
`Field` (Mathlib.Algebra.Field.Defs);
`AlgebraicGeometry.IsProper` (Mathlib.AlgebraicGeometry.Morphisms.Proper);
`AlgebraicGeometry.RingedSpace.IsCoherent` (Sheaf.AlgebraicGeometry.Coherent);
`AlgebraicGeometry.Scheme.Modules.IsInvertible`, `tensorPow`
(WeilConjectures.AlgebraicGeometry.Modules.Invertible);
`topologicalKrullDim` (Mathlib.Topology.KrullDimension);
`irreducibleComponents` (Mathlib.Topology.Irreducible);
`AlgebraicGeometry.IsIntegral` (Mathlib.AlgebraicGeometry.Properties);
`AlgebraicGeometry.IsClosedImmersion` (Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion);
`IsGenericPoint` (Mathlib.Topology.Sober);
`Module.length` (Mathlib.RingTheory.Length);
`AlgebraicGeometry.Scheme.Modules.eulerChar`
(WeilConjectures.AlgebraicGeometry.Cohomology.Defs).
Additional existing construction declarations are `Scheme.Modules.dual`
(WeilConjectures.AlgebraicGeometry.Modules.Dual), `Scheme.Modules.pushforward`
(Mathlib.AlgebraicGeometry.Modules.Sheaf), and the stalk module instance
(WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk).
Their full source signatures and docstrings were inspected. The three new definition
modules are imported and used; no dependency notion has a private replacement.

Edge cases checked mathematically: r=0 is the empty tensor family and a polynomial
in no variables, so only constants remain; s=0 gives an empty sum and vacuous length
clauses. F=0 or X empty gives S empty, d=bottom, no components and the zero function;
the polynomial predicate admits the zero polynomial even at bottom. For d=0 it forces
zero, as required. Negative exponents use (dual L)^(a+1) for Int.negSucc a, so n=-1
is the dual and n=0 is the tensor unit. There is no characteristic restriction on k.
The dimension and sheaf universes are explicit, and there are no auto-bound variables.
No disputed statement or unusable dependency record was found.

Searches made (machine-readable originals in searches.jsonl):

- LeanFinder, `Euler characteristic coherent sheaf leading term numerical polynomial generic lengths`:
  eight unrelated results (Lie-module degrees, constructible degBound, incidence-algebra
  Euler characteristic, Hilbert polynomial); no statement match.
- Loogle, `MvPolynomial.totalDegree, Module.length`: zero hits.
- msearch grep, `NumericalPolynomial|numerical.polynomial|leading.term`, AlgebraicGeometry:
  only three elliptic division-polynomial hits, not this statement.
- LeanSearch, `integer valued multivariate rational numerical polynomial`: service unavailable.
  LeanFinder with the same query: Dioph IsPoly/Poly and Witt polynomials; none represent
  integer-valued rational polynomial functions. msearch grep
  `NumericalPolynomial|numerical.polynomial|IntegerValued`: zero hits.
- LeanSearch, `integer tensor power invertible sheaf dual negative powers`: unavailable.
  LeanFinder with this query: CommRing.Pic tensor/dual operations for ring modules, not
  scheme module sheaves. msearch grep `tensorPowInt|tensorZPow|integer.*tensor|tensor.*integer`:
  zero hits.
- LeanSearch, `support sheaf modules scheme nonzero stalks`: unavailable.
  LeanFinder with the same query: IdealSheafData support (the vanishing locus of an ideal,
  not the nonzero-stalk support of a module), and basicOpen evaluation results; no match.
  msearch grep `def.*support|def.*Support|abbrev.*support` in Topology/Sheaves: zero hits.
- rg in source WeilConjectures and local lean/Sheaf for numerical-polynomial names,
  integer tensor-power names and support definitions: existing natural tensorPow and
  dual were reused; no multiple-integer-twist, numerical-function predicate or
  Zariski module-stalk-support declaration. Node-id search in WeilConjectures found
  no declaration for this item. dag/lean_names_upstream.json has none of the new names.
- DAG searches for numerical-polynomial definitions and integer tensor twists found
  none. blueprint_refs.py search `numerical polynomial` finds Hilbert polynomial and
  Hilbert degree, neither defines numerical polynomiality. Search `tensor power`
  gives six unrelated/specialized items. Search `support` gives numerous statements,
  while searches `support of a coherent` and `support of a module` give zero.
  The existing def-kun-support was read: it is geometric-stalk support of etale sheaves,
  and is a different notion from Zariski O_X-module support.

Validation: all modules are compiled together by the mandated scompile.py tool;
no local compilation is performed. The initial combined compile exposed duplicate
universe names from concatenated module bodies; the support and twist modules now
use distinct explicitly declared universe names. The final dry run result is recorded
by deliver2.py; no push or second-reading section is performed by this worker.

## New nodes

`def-sc-multi-tensor-twist` defines the ordered multi-twist in the displayed expression
of Tag 0BEN, citing def-sc-invertible-module for invertible sheaves and their duals.
It reuses existing tensorPow, dual, and the scheme module monoidal structure; only
iteration with integer exponents is new. Searches above found no existing node or
declaration for it. The extension of the formula to arbitrary modules adds no
hypothesis to the theorem, which still requires every L_i to be invertible.

`def-sc-numerical-polynomial-degree-lt` defines the conclusion of Tag 0BEN as an
integer-valued function represented by a rational polynomial on the whole integer
lattice, with the strict monomial degree bound. It cites the extended dimension
notion def-kun-topological-krull-dimension. No equivalent predicate exists in the
DAG, project or Mathlib; the existing MvPolynomial representation is reused.

`def-sc-module-stalk-support` defines the support in Tag 0BEN as the nonzero-stalk
locus, citing def-pc-scheme. It uses the existing presheaf stalk rather than creating
a stalk carrier. IdealSheafData.support and def-kun-support were checked and do not
define this notion. All three definition nodes have the item's chapter and unit,
the ancestor lem-sc-mult-n-finite-flat, and the required via chain and search records.

Dry-run repair: the latest server base has one additional ancestor-path entry,
lem-sc-positive-ample-hilbert-degree; all new nodes now use that complete via chain.
The canonical signature reader starts at the declaration keyword `def`, so the
multi-twist record excludes the modifier `noncomputable` (the definition itself
remains noncomputable). No mathematical statement changed.

## Second reading by J1

I independently read the item node, all its statement-dependency nodes and their
recorded declaration signatures, the three proposed new nodes and their module
bodies, and the complete Stacks `varieties.tex` lemma and proof at
`lemma-numerical-polynomial-leading-term` (Tag 0BEN). The TeX was fetched read-only
from the Stacks source; Section 0BEL was also read for the surrounding hypotheses
and numerical-polynomial convention. The source imposes no additional ambient
hypothesis beyond a field, properness, coherence, and invertibility.

The node's complete object/hypothesis/conclusion list, matched against the final Lean:

- A field k: `k : Type u` and `[Field k]`. Exact; arbitrary characteristic.
- A proper scheme X over k: `X : Scheme.{u}`, `[X.Over (Spec (.of k))]`,
  `[IsProper (X ↘ Spec (.of k))]`. Exact; neither integrality nor projectivity
  is required of X. Mathlib properness includes universal closedness, separatedness,
  and local finite type; universal closedness supplies quasi-compactness.
- A coherent O_X-module F: `F : X.Modules` and
  `hF : RingedSpace.IsCoherent X.toRingedSpace F`. Exact. I opened Coherent.lean:
  finite type and finite-type kernels on every open of all maps from finite free
  modules, on the same module-sheaf carrier as X.Modules.
- Invertible modules L_1,...,L_r: `r : ℕ`, `L : Fin r → X.Modules`, and
  `[∀ i, (L i).IsInvertible]`. Exact. The recorded scheme-module invertibility
  class is local triviality on an open neighbourhood, with the structure sheaf as unit.
- Support of F: `S : Set X`,
  `hS : S = {x | Nontrivial (F.presheaf.stalk x)}`. Exact nonzero-stalk locus,
  on the Zariski space of X and its existing underlying abelian sheaf; no invented
  stalk carrier or geometric/etale stalk is used.
- Its dimension d: `d : WithBot ℕ∞`, `hd : d = topologicalKrullDim S`.
  Exact subspace dimension, including empty support. I checked the definition
  as the order Krull dimension of irreducible closed subsets.
- All dimension-d irreducible components: `s : ℕ` and `components : Fin s ≃
  {C : Set S // C ∈ irreducibleComponents S ∧ topologicalKrullDim C = d}`.
  Exact finite enumeration, without omissions or repetitions. The source's proper
  scheme is Noetherian, so choosing such an enumeration adds no finiteness assumption.
- Their reduced integral closed-subscheme structures: `Z : Fin s → Scheme.{u}`,
  `[∀ i, IsIntegral (Z i)]`, `ι : ∀ i, Z i ⟶ X`,
  `[∀ i, IsClosedImmersion (ι i)]`, and
  `hι : ∀ i, Set.range (ι i) = Subtype.val '' (components i).val`.
  Exact: an integral closed subscheme is reduced, and the reduced closed subscheme
  with this underlying set is unique over X. No additional structure map over k is
  needed for Z: both Euler characteristics in the node are on X.
- Generic points ξ_i: `ξ : Fin s → X` and
  `hξ : ∀ i, IsGenericPoint (ξ i) (Set.range (ι i))`. Exact ambient generic points;
  closure of the singleton equals the component, which also ensures membership.
- Multiplicities m_i are the local lengths and positive integers:
  `∃ m : Fin s → ℕ`, together with
  `∀ i, Module.length (X.presheaf.stalk (ξ i)) (F.presheaf.stalk (ξ i)) =
  (m i : ℕ∞) ∧ 0 < m i`. Exact: equality asserts finite length, identifies each
  length, and positivity is separate. The stalk module instance was opened and
  acts by the existing O_X stalk on the existing underlying abelian stalk.
- Every integer tuple n: the function in the final predicate has domain `Fin r → ℤ`.
  Exact; neither an eventually-polynomial assertion nor a natural-exponent restriction.
- Twisted χ(X,F): `(multiTensorTwist F L n).eulerChar k`. Exact, using the dependency's
  recorded Euler characteristic, whose body is the alternating finsum of k-finranks.
  Proper coherent sheaves have finite-dimensional, eventually zero cohomology; the
  existing abelian-sheaf encoding is the recorded Euler-characteristic definition.
- Subtract all weighted component contributions: the `∑ i : Fin s, (m i : ℤ) * ...`
  term twists `(pushforward (ι i)).obj (SheafOfModules.unit _)` with the same L,n.
  Exact i_*O_Z and the exact pushforward form the node specifies. I opened the
  pushforward definition and its sections formula, and the dual definition.
- A numerical polynomial of total degree < d: `IsNumericalPolynomialDegreeLT ... d`.
  Exact: one rational polynomial P, equality at every integer tuple, and the sum of
  exponents of each monomial in P.support strictly less than d. The polynomial is
  allowed to be zero, even at d=0 or bottom, and there is no natural subtraction.

Edge cases: r=0 has one integer tuple and an empty fold returning F; s=0 has an empty
sum and vacuous generic-length clauses. For F=0, or X empty, S is empty, its dimension
is bottom, and the component type is empty. The zero polynomial satisfies the predicate
at bottom. For d=0 every nonzero monomial has degree at least zero, so the strict bound
forces P=0. Exponents 0 and -1 use the tensor unit and the dual respectively; all
negative integers are covered by `Int.negSucc`. No characteristic case is dropped.
All universe names are explicitly declared. k, X, modules and component schemes use
the project's arbitrary common universe u; no independent smaller testing universe
or fixed universe level is introduced. No variable is auto-bound.

Independent searches (also recorded by msearch in searches.jsonl): LeanFinder
`coherent sheaf Euler characteristic top dimensional components multiplicities polynomial`
returned incidence-algebra Euler characteristics, basic-open facts, and a constructible
set degree bound, none matching this theorem. Loogle `MvPolynomial.eval, ℚ` returned
zero results. LeanFinder searches with `integer exponents tensor products line bundles
inverse dual sheaf` and `integer lattice function represented rational multivariate
polynomial bounded monomial degree` checked the two remaining new notions independently.
I used rg with `integer.?valued`, `numerical.?poly`, `multi.?twist`,
`tensor.*(zpow|integer)`, `support.*stalk`, `stalk.*support`, and definition-name patterns
on Mathlib, WeilConjectures and lean/Sheaf. Existing natural tensorPow and dual are used.
The source Hilbert polynomial theorem in Modules/Ample.lean was opened: it is univariate,
ample, structure-sheaf, and natural-exponent only, so is not the item. Module.support
is support of an ordinary ring module on PrimeSpectrum, IdealSheafData.support is a
vanishing locus, and WeilSheaf.support is on finite points; none is this scheme-module
support declaration. The project's etale support modules concern geometric stalks.

Mismatch found and repaired (H12): the proposed new `def-sc-module-stalk-support`
duplicates clause (2) of the existing DAG node
`def-weil-pbc-closed-subset-proper-over-base`. I opened that entire node: it already
states exactly the nonzero Zariski module-stalk locus, sourced to Stacks 01AT, although
it has no recorded Lean declaration. A new support definition node is therefore
unjustified. I deleted its node and ModuleStalkSupport.lean, removed its import and
added stmt_dep, and replaced `S = stalkSupport F` by the literal nonzero-stalk set
in the binder introducing S. This supplies the already specified set without any
new named definition or duplicate DAG node. It does not alter the item's mathematical
statement or its hypotheses/conclusions. The item lean.statement was updated verbatim.
The earlier Worker report and New nodes section are retained as the worker's history;
the delivered new nodes are only the two listed in the next paragraph.

The remaining new definition nodes were read as stage-1 definitions. The multi-twist
node describes exactly the ordered left-associated displayed tensor product, with
nonnegative powers from tensorPow and negative powers from the existing dual; its
extension to arbitrary modules is explicitly documented, while the item requires
invertibility. The numerical-polynomial node gives the integer-valued rational
polynomial notion used by 0BEN/0BEL and extends the degree bound to the recorded
WithBot ℕ∞ dimension convention without excluding zero. Neither notion already has
a DAG definition or matching project/Mathlib declaration. Both have complete concrete
bodies, correct chapter/unit and ancestor/via fields, three search kinds, null match,
empty proof fields, created records and complete lean records. No dependency module
is delivered. No corrected item statement or statement_change was present or needed.

Docstrings and conventions: every retained declaration and module names its source and
blueprint node; the theorem docstring carries each of the node's five proof steps with
its dependencies. Only the item theorem has `sorry`; nothing is proved and neither
new definition has postponed data. All imports are used, all lines fit the limit, and
namespace and file names follow the project's conventions. Combined server compilation
was rerun after the repair on all three remaining modules. The dry run and actual
delivery below are performed through the required deliver2.py tool.
