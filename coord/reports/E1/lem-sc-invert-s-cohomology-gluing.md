## Worker report

The module `Sheaf.AlgebraicGeometry.CohomologySectionLocalizationGluing` states
`AlgebraicGeometry.Scheme.Modules.cohomologySectionLocalization_gluing`, with its
only proof `sorry`. The added definition module gives the numerator formulation of
bijectivity of the canonical localization comparison, with no postponed data or proofs.
There is no statement correction and no dependency replacement.

Hypothesis and clause correspondence:

- The scheme Y is `X : Scheme.{uG}`. Its quasi-compactness is `[CompactSpace X]`;
  quasi-separatedness is `[QuasiSeparatedSpace X]`. These are the Mathlib notions named
  by the two convention dependencies, not conditions on an identity morphism.
- The invertible module is `L : X.Modules` with `[L.IsInvertible]`; the global section is
  `s : Γ(L, ⊤)`. The quasi-coherent module is `F : X.Modules` with `[F.IsQuasicoherent]`.
- The nonvanishing open Y_s is `S : X.Opens` with
  `hS : (S : Set X) = nonvanishingLocus L s`. This names the node's already specified
  open, not a new geometric restriction. The open exists for every invertible L and s
  by Stacks Modules 01CY, and its underlying set determines it uniquely. Using a named
  open with this equation follows SectionRestrictionSTorsion and
  SectionClearingDenominatorsQCQS in this library.
- W is an `X.Opens`; W_s is `W ⊓ S`. Cohomological degrees p and denominator powers
  n,b are arbitrary naturals, including zero.
- The numerator in degree n is the object
  `(RingedSpace.openModuleCohomology X.toRingedSpace p W).obj
  (F ⊗ L.tensorPow n : X.Modules)`. This is exactly H^p(W,F|_W ⊗ L|_W^n): restriction
  of tensor products and tensor powers agrees with tensoring restrictions. It is not
  a different cohomology theory.
- The nonnegative powers are the dependency's existing `L.tensorPow n`. The node's
  negative tensor powers and its graded ring action are not separately redefined:
  every degree-zero fraction has numerator degree n >= 0 and denominator s^n.
  All comparisons and their bijectivity depend only on these components and the
  transitions given by multiplying with s. A finite sum of such fractions is a single
  fraction after passing to a common denominator. Negative components in the Z-graded
  module create no additional degree-zero fractions or relations.
- The canonical formula c(x/s^n) = s^(-n)x is expressed without choosing an inverse:
  multiplication by s^n on W_s takes c(x/s^n) to x restricted to W_s. The multiplication
  morphism is `(ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n`, mapped by
  `openModuleCohomology`. Since s trivializes L on S, this multiplication is invertible
  on W_s and determines exactly the canonical comparison, not an arbitrary map.
- `IsCohomologySectionLocalization L F s S W p` has two clauses. Its first clause says
  every y on W_s has n and x with res(x) = s^n y (surjectivity of c). Its second clause
  says res(x) = 0 implies some s^b x = 0 (injectivity of c). Indeed, a fraction x/s^n
  is zero exactly when a further power of s kills its numerator; and c(x/s^n) is zero
  exactly when res(x) = 0, since multiplication by s^n on W_s is invertible.
  This is precisely bijectivity of the canonical linear map, hence its being an
  isomorphism of modules; no scalar compatibility hypothesis is dropped, because
  linearity is inherent in the canonical restriction/tensor multiplication map.
- U and V are `U V : X.Opens`. Quasi-compact U is `hU : IsCompact (U : Set X)`;
  affine V is `hV : IsAffineOpen V`.
- `h_locU`, `h_locV`, and `h_locUV` assert the comparison criterion for every p on
  U, V and `U ⊓ V`. The conclusion asserts it for every p on `U ⊔ V`. The same L,F,s,S
  occur in all four places.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Opens`;
  Scheme.Hom's signature was also read. These supply the schemes and opens.
- WeilConjectures.AlgebraicGeometry.Modules.Invertible:
  `Scheme.Modules.IsInvertible`, `tensorPow`, `tensorPowAddIso` and the scheme-module
  monoidal instance. The quasi-coherent and dual portions of the dependency are not
  redefined. Dual negative powers are unnecessary in the fraction presentation.
- Sheaf.AlgebraicGeometry.Coherent: its docstring identifies the node's quasi-coherent
  clause as Mathlib `SheafOfModules.IsQuasicoherent`; its `IsCoherent` signature was read.
  The theorem uses that quasi-coherent clause, without adding coherence or finite type.
  Direct import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent supplies it.
- Sheaf.Paper.PQFCohomology: read `sheafCohomologyAndHigherDirectImages` and its docstring;
  it uses the shared RingedSpace.moduleCohomology. The more specific open cohomology
  dependency below supplies the actual H^p(W,-) and restrictions used here. No extra
  import of the unused higher-direct-image theorem is needed.
- Sheaf.AlgebraicGeometry.Ample: `Scheme.Modules.nonvanishingLocus`; read `IsAmple` too.
  No ampleness hypothesis is introduced.
- Mathlib.Topology.Defs.Filter: `CompactSpace` (no separation axiom).
- def-weil-pbc-scheme-conventions is explicitly a convention node with no declaration;
  use its named Mathlib meanings. QuasiSeparatedSpace is the equivalent scheme notion,
  read in Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated.
- Sheaf.Topology.OpenModuleCohomology (def-sc-open-module-cohomology):
  `RingedSpace.openModuleCohomology`, `openModuleCohomologyRestriction`; the functors
  are right derived sections on opens and restrictions are derived restriction.
- WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator:
  `Scheme.Modules.homOfGlobalSection` (r maps to r times s).
- WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators:
  `tensorPowSection`, `mulTensorPowSection`. These are the actual multiplication maps,
  with existing associators and tensorPowAddIso, not unspecified transition maps.

Edge cases checked before writing: p = 0 uses derived degree zero, not a positive-degree
restriction. n = 0 uses the tensor unit and its right unitor. b = 0 is permitted in the
torsion criterion. Empty W has zero cohomology on both sides. Empty X and F = 0 likewise
have zero comparison groups. For s = 0, S is empty; every numerator is killed after one
further multiplication, so the comparison criterion correctly identifies both sides as
zero. For a nowhere vanishing s, S is top and every class has exponent-zero numerator,
while restriction kernels are zero. U = V, V contained in U, and empty intersections
are admitted. No finite dimensionality, Noetherianity, separatedness, ampleness, or
positivity of p is imposed. One explicit scheme universe covers all modules and opens;
there is no independently smaller testing universe and no auto-bound variable.

Searches (raw service records retained in searches.jsonl):

- msearch leanfinder: `Mayer Vietoris gluing localization graded sheaf cohomology
  invertible sheaf section`: eight unrelated gluing/Proj hits, no matching statement.
- msearch loogle: `GradedModule, Localization`: no hits; unknown GradedModule identifier.
- msearch grep: `GradedModule|degreeZero|DegreeZero|localization.*cohomology`: three
  graded-module namespace hits, no graded scheme-cohomology comparison.
- msearch leansearch: `sheaf module global section morphism from unit tensor
  multiplication`: service unavailable (Internal Server Error).
- msearch leansearch: `degree zero localization of tensor power cohomology at invertible
  sheaf section fractions clearing denominators`: service unavailable.
- msearch leanfinder: `cohomology localization is bijective iff every class has a
  denominator and restriction kernel is section power torsion`: eight categorical
  localization or ordinary ring-localization hits, none for twisted scheme cohomology.
- msearch grep: `CohomologySectionLocalization|cohomology.*fraction|fraction.*cohomology`:
  zero Mathlib hits. The identical rg search in WeilConjectures and lean/Sheaf has only
  unrelated fraction-field cohomology docstrings, no matching definition.
- rg and the required item-id search in WeilConjectures: no occurrence of this item.
  Broad searches in lean/Sheaf found SectionFractionPresentation and
  InvertibleSectionLocalization, which concern sections (degree zero), not all p.
  They were opened and read; the former's fractions relation agrees with our transition.
- DAG rg for cohomology fractions/denominators found statements about the localization
  theorem and its proof ingredients, but no definition node giving this criterion.
  tools/blueprint_refs.py search 'cohomology localization' returned zero blueprint nodes.
  The exact new id/name search in DAG, upstream-name index, Mathlib, WeilConjectures and
  lean/Sheaf returned no collision.

The Stacks source is not installed in this clone's literature directory. Read the actual
source at https://stacks.math.columbia.edu/tag/09MR: its proof uses P(U),P(V),P(U∩V),
the Mayer--Vietoris comparison diagram and the five lemma, exactly as the node says.
The theorem docstring carries this proof with its two proof-dependency ids.

Validation: the two modules compiled together on the server under the default timeout,
with no errors or warnings, in 2.5 seconds. Explicit X.Modules type annotations keep the
existing scheme-module tensor instance; @id merely supplies the morphism type and is
not a statement-local definition or hidden let.

## New nodes

`def-sc-cohomology-section-localization` defines the two fraction conditions in every
cohomological degree and on every open. Source: Stacks 09MR's canonical comparison
formula and Properties Section 0B5K's fraction convention. It uses the existing
open-module-cohomology and tensor-power definitions, so no second cohomology, tensor
power, section ring, or localization implementation is introduced. The node records the
actual service searches above. No DAG definition node or Lean declaration supplies this
criterion for all p: SectionFractionPresentation and its localization theorem supply
only section fractions, while generic Mathlib module localizations do not have the
scheme's graded tensor-power cohomology data. The new definition has no sorry and its
only purpose is to state exactly the item's canonical-comparison isomorphism conditions.

## Second reading by E1

I reread the item node, its Stacks source (09MR), the dependency records, and both
 delivered modules. The statement's objects and hypotheses correspond as follows:

- The scheme `Y` is rendered by `X : Scheme.{uG}`, with `[CompactSpace X]` and
  `[QuasiSeparatedSpace X]`, exactly the quasi-compact and quasi-separated assumptions.
- The invertible module, section, and quasi-coherent module are rendered by
  `L : X.Modules`, `[L.IsInvertible]`, `s : Γ(L, ⊤)`, `F : X.Modules`, and
  `[F.IsQuasicoherent]`; no Noetherian, separated, finite type, or ampleness hypothesis
  is added.
- The nonvanishing open is `S : X.Opens` with
  `hS : (S : Set X) = nonvanishingLocus L s`. For each open `W`, the intersection
  `W_s` is `W ⊓ S`, and tensor powers, restrictions, and degree `p` cohomology are
  rendered by the recorded `tensorPow`, `openModuleCohomology`, and restriction maps.
- The source's canonical fraction comparison `c^p_W` is rendered by
  `IsCohomologySectionLocalization L F s S W p`. Its first conjunct is precisely
  surjectivity (every class on `W_s` is the restriction of a numerator multiplied by
  `s^n`), and its second conjunct is precisely injectivity (a numerator restricting to
  zero is killed by some further `s^b`). Thus it is the stated bijectivity condition,
  including the canonical multiplication maps, rather than an unrelated predicate.
- `U` and `V` are `X.Opens`, with `hU : IsCompact (U : Set X)` and
  `hV : IsAffineOpen V`; the three hypotheses quantify over every `p : ℕ` on `U`,
  `V`, and `U ⊓ V`, and the conclusion quantifies over every `p` on `U ⊔ V`.
  The quantifier order and all three premises are unchanged.

The proof docstring records the source proof: the Mayer–Vietoris ladder has exact rows,
the outside comparison maps in adjacent degrees are isomorphisms by the three premises,
and the five lemma gives the union comparison. No statement mismatch was found and no
statement correction was made. The only representational point checked was that the
new predicate replaces the source's fraction-map notation; its two conjuncts are the
explicit numerator characterization of that same map, and the equality `hS` identifies
the chosen open with `X_s`.

Edge cases checked: `p = 0`, `n = 0`, and `b = 0` are admitted; empty opens and the
empty scheme reduce to zero cohomology; `F = 0` is allowed; `s = 0` gives the empty
nonvanishing open; a nowhere-vanishing `s` gives `S = ⊤`; `U = V`, containment, and
empty intersections are allowed. No characteristic or positivity assumption is present,
and the single universe `uG` covers the scheme, modules, and opens without an
independently smaller testing universe.

Searches were reread from `searches.jsonl` and repeated with `rg` over Mathlib,
`WeilConjectures`, `lean/Sheaf`, and the DAG, plus LeanFinder/Loogle/msearch queries
for Mayer–Vietoris localization and cohomology fractions. They found no existing
declaration of this theorem or of the all-degree tensor-power cohomology fraction
criterion. The existing section-fraction and generic localization declarations concern
different notions and were not duplicated.

The two modules compile together with `scompile.py` under the default timeout, with no
errors or warnings other than the expected `sorry` theorem proof.
