## Worker report

The module `Sheaf.Paper.SfClosedPartitionModuleTest` states
`AlgebraicGeometry.Scheme.sf_closed_partition_module_test`, with its sole theorem
proof `sorry`. The real helper definition `sfClosedPartitionRestrictionIso`
composes the published canonical pullback compositor with the pullback of the
supplied closed restriction isomorphism. Its data contains no postponed proof.
The geometric output partition is chosen before the coefficient modules, so the
same extension of the supplied partition works for every such module.

Hypothesis and clause correspondence:

- Noetherian X: `{X Z U : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]`.
- Closed i and complementary open j: the two morphisms with `[IsClosedImmersion i]`,
  `[IsOpenImmersion j]`, and `hji : Set.range j = (Set.range i)ᶜ`.
- The finite stratification of Z is `S : FiniteLocallyClosedStratification Z`;
  `hS` supplies constructibility of every image. The structure already supplies
  local closedness, pairwise disjointness, coverage and immersions realizing images.
- Every open is retrocompact and quasi-compact: the first universal conjunct over
  open `V : Set X` is `IsRetrocompact V ∧ IsCompact V`. The next is `QuasiCompact j`.
- The extended partition is `R : Stratification X`. This published structure
  includes constructibility and local closedness. `e : Fin (S.n + 1) ≃ Fin R.n`
  and equality of dependent scheme/morphism pairs with `Fin.snoc` require exactly
  the old schemes and composite immersions, followed by the given U and j.
  Equality, rather than just an isomorphism of domains, preserves scheme structures.
- Finite commutative coefficients are `(A : Type u) [CommRing A] [Finite A]`.
  P and N are `proEtaleRingModules` over `proEtaleConstantRing`, the actual
  sheafification of the constant ring presheaf (with the conventional ULift).
- The closed identification is `h : proEtaleConstantModulePullback i A P ≅ N`.
  `hzero : IsZero (proEtaleConstantModulePullback j A P)` expresses the supplied
  zero restriction, equivalently its isomorphism with the zero object. A map to
  a zero object is unique, so this loses no choice relevant to the statement.
  IsZero also avoids an unresolved universe in the library's chosen-zero instance.
- The helper's two factors are the canonical composition comparison evaluated at P
  and `(proEtaleConstantRingPullback A t).mapIso h`. The published compositor is
  normalized by its direct-image mate on fibre-product sections. Its functor
  isomorphism supplies naturality and the sheaf-module category supplies linearity.
  The first module conjunct asserts these restriction isomorphisms for every μ.
- The new open stratum is explicitly isomorphic to `proEtaleConstantModuleSheaf`
  of the zero module, not just an unspecified locally constant model.
- The conditional hypothesis is local constancy of each pullback of N, using the
  dependency's `IsLocallyConstantProEtaleModuleSheafOfUniverses.{u,u}`, and
  `Finite` of `proEtaleGeometricModuleStalk` for every algebraically closed field
  Ω in the scheme universe and point y of its domain.
- The conclusion gives `0 < R.n` and the local-constancy and finite-geometric-stalk
  conditions on this same R, together with the published intrinsic predicate
  `IsConstructibleProEtaleModuleSheaf X A P`. The latter is publicly available
  from the recorded constructibility module and is listed in that node's
  declarations; the primary fixed-module predicate is not substituted for it.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, via the Noetherian import.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion` (transitive imports).
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Topology.FiniteLocallyClosedStratification` and
  `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification`.
- `Mathlib.Topology.Constructible`: `Topology.IsConstructible`, `IsRetrocompact`;
  `Mathlib.Topology.Defs.Basic`: `IsLocallyClosed`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`;
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleConstantRing`,
  `proEtaleConstantModulePullback` (canonical inverse image and tensor extension).
- `Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses`:
  `IsLocallyConstantProEtaleModuleSheafOfUniverses`; publicly imports its
  common-universe version `IsLocallyConstantProEtaleModuleSheaf` and
  `proEtaleConstantModuleSheaf` used by the intrinsic constructibility predicate.
- `Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor`: publicly imports
  `proEtaleGeometricModuleStalk`, the module colimit used by its functor.
- `Sheaf.Paper.ProEtaleFixedModuleConstructible`: publicly imports
  `IsConstructibleProEtaleModuleSheaf` from ProEtaleConstructibleSheaf.
- `Sheaf.Paper.ProEtaleCoefficientModulePullbackComposition`: publicly imports
  `proEtaleConstantRingModulePullbackComposition` and the actual constant-ring
  pullback functor, used in the helper. The independently sized compositor is
  retained by this recorded import, but a coefficient universe enlargement is
  unnecessary for finite rings in this common-universe presentation.
- Proof-only import `Sheaf.AlgebraicGeometry.NoetherianComplementaryStratifications`:
  `noetherian_complementary_stratifications`, whose entire signature and proof
  docstring were read. It is precisely the geometric assembly step of this node.

Sources read: schemes.tex lemma-composition-immersion (02V0), properties.tex
lemma-locally-Noetherian (01OW) and lemma-Noetherian-topology (01OZ), topology.tex
lemma-Noetherian-quasi-compact (04ZA), and sites-modules.tex
lemma-push-pull-composition-modules (03D8). The module docstring transcribes the
three reviewed proof steps, including the zero-sheaf and stalk arguments.

Edge cases checked before writing: S.n = 0 forces Z empty and the output has one
stratum U; empty U remains as an empty stratum; empty X admits the one-empty-stratum
case. Empty old strata remain literal original schemes. The zero coefficient ring,
zero P and zero N are allowed. No reducedness, positive dimension, nonempty scheme,
nonzero coefficient, finite presentation, or etale-origin hypothesis is imposed.
The coefficient and geometric point conventions agree with the published intrinsic
predicate; object and morphism universes of the small pro-etale site are not equated.
No statement correction, new node or dependency repair was needed.

Searches performed with msearch.py (recorded in searches.jsonl):

- leanfinder, `Extend closed subscheme finite stratification by open complement and
  test constructibility of proetale module sheaves`: eight hits, concerning affine
  covers, section vanishing and etale topology; no whole-statement match.
- loogle, `"SheafOfModules.pullbackComp"`: the presheaf and sheaf generic
  pullback-composition declarations, neither this scheme partition/module test.
- grep, `closed.*[Pp]artition|closed.*[Ss]tratif`, Mathlib/AlgebraicGeometry:
  zero hits.
- leansearch, `Constructibility of proetale module sheaves using a finite
  stratification of a closed subscheme and zero restriction to its open complement`:
  eight hits about ordinary scheme modules; no matching pro-etale theorem.
- rg of the project and upstream sources for closed partitions/stratifications,
  and the item id: the geometric theorem above, FiniteImmersionConstructibilityInterval
  and other constructibility results. The older finite-immersion closed-partition
  predicate concerns the particular sheaf i_*N and uses isomorphic domains; it does
  not state this test for arbitrary supplied P and its exact original domains.
- grep -rn of the item id in lean/WeilConjectures and rg in
  dag/lean_names_upstream.json: no attachment or declaration for this item.

## Second reading by Q78

This is a self-audit after reopening the node and module; no separate agent was
started, as instructed. The maintainer's independent review remains required.
The hS assumption was retained even though Noetherianity makes it redundant for
this theorem. Checked the two different stratification interfaces: the input
FiniteLocallyClosedStratification has no hidden constructibility field, while the
output Stratification carries exactly the required constructible locally closed
images. Checked Fin.snoc ordering and dependent-pair equality, which preserve the
original schemes rather than their reductions. Checked that the final witness is
on the same R, rather than merely existential constructibility on another partition.
Checked local-constancy universe arguments explicitly and changed the zero-object
binder to the equivalent IsZero form after isolating the existing zero-instance
universe error in a module-mode probe. The canonical restriction helper uses the
published normalized compositor; no arbitrary coefficient map or iso is supplied.

Validation: scompile.py accepted the delivered module in sandbox and library modes
with no errors or non-sorry warnings. deliver2.py --no-push printed OK for commit
7ca66a140a2, passing server preflight and per-file compilation. A local structural
check confirms only `lean` differs in the node copy, its signature is verbatim,
all Lean lines are at most 100 characters, and exactly one theorem has `sorry`.
