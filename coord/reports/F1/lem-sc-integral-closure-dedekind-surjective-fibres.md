## Worker report

The module states `AlgebraicGeometry.integralClosure_isDedekind_surjective_finite_fibres`.
It uses `A`, `K`, and `L` as commutative/domain/field rings, with `K` a fraction
field of `A`, `L` an algebraic finite-dimensional extension of `K`, and the scalar
tower and Noetherian hypotheses. The hypothesis `hA : ringKrullDim A = 1`
renders the one-dimensional Krull-dimension clause. The local `C` is Mathlib's
`integralClosure A L`; `f` is the spectrum morphism induced by `algebraMap A C`.
The four conclusion clauses render, respectively, that `C` is a Dedekind domain,
that `f.base` is surjective, that each set-theoretic fibre is finite, and that each
residue-field map is a finite ring hom.

The dependency notion of integral closure is Mathlib's `integralClosure` (the
recorded dependency node identifies it). No project declaration was duplicated.
The Dedekind predicate is Mathlib's `IsDedekindDomain`; Noetherianity is
`IsNoetherianRing`; and dimension is Mathlib's `ringKrullDim`. Spectrum and
residue-field maps are Mathlib's `Spec`, `Scheme.Hom.base`, and
`Scheme.Hom.residueFieldMap`.

Edge cases checked: the dimension hypothesis excludes the zero ring; the theorem
allows arbitrary universe-`u` rings and fields, including the generic fibre and
zero-dimensional special fibres; no nonempty index or finiteness assumption is
silently added beyond the stated finite-dimensional extension.

Searches made: `msearch.py leanfinder` for integral-closure Dedekind finite
surjective fibres found only `IsIntegralClosure.isDedekindDomain` (requires a
Dedekind base) and no fibre theorem; `msearch.py loogle` for
`IsIntegralClosure, IsDedekindDomain, finite` returned no declaration; grep of
Mathlib for `IsIntegralClosure.*finite|isDedekindDomain|finite.*fiber` found
only the separate integral-closure Dedekind results. `rg` over the source and
`lean/Sheaf` found no matching project theorem. The module compiles remotely with
only the expected `sorry` proof warning.

## Earlier second reading (a previous round; superseded)

Reading the node and module independently, every node hypothesis has a binder:
commutative domain, fraction field, field extension, scalar tower,
finite-dimensionality, Noetherianity, and dimension one. The conclusion's
Dedekind, surjectivity, finite-fibre, and finite-residue-extension clauses each
have a direct Lean counterpart. The only translation choice is Mathlib's
`Finite` predicate on the fibre subtype and `RingHom.Finite` on residue maps,
which are the standard formal meanings of the source's finite fibres and finite
residue-field extensions. No mismatch was found.

## Second reading by F1

I independently opened the node, its delivered Lean file, all four statement
 dependency nodes, and their Mathlib declarations. I read Stacks algebra.tex on
 the server at `lemma-integral-closure-Dedekind` (09IG), including its proof and
 the enclosing Factorization section. There are no additional standing hypotheses
 in that section: 09IG explicitly introduces its own Noetherian domain, dimension,
 fraction field and finite extension. The node agrees with the source; no node
 statement correction, new definition node, or dependency module is needed.

Object/hypothesis/conclusion checklist, in node order:

- Commutative domain A: `(A L : Type u)` with `[CommRing A] [IsDomain A]`.
  Correct; domains here have 1 distinct from 0.
- A Noetherian: `[IsNoetherianRing A]`. Correct: the dependency points to
  Mathlib.RingTheory.Noetherian.Defs, `IsNoetherianRing := IsNoetherian A A`,
  meaning all ideals are finitely generated (Defs.lean:196).
- A has Krull dimension exactly 1: `hA : ringKrullDim A = 1`. Correct:
  Mathlib.RingTheory.KrullDimension.Basic defines `ringKrullDim` as the supremum
  of lengths of strict prime chains, with bottom for the zero ring (line 30).
- Fraction field K of A: `(K : Type v) [Field K] [Algebra A K]
  [IsFractionRing A K]`. Correct: this is the domain's fraction field, not an
  arbitrary extension or an extra normality hypothesis on A.
- Finite field extension L/K: `[Field L] [Algebra K L]
  [FiniteDimensional K L]`. Correct; no separability or characteristic constraint.
- A included in L compatibly: `[Algebra A L] [IsScalarTower A K L]`.
  Correct: these supply the composite A -> K -> L, not a stronger hypothesis.
  Field maps and the fraction-ring embedding make it injective.
- Integral closure C: `let C := integralClosure A L`. Correct: the dependency
  Mathlib.RingTheory.IntegralClosure.Algebra.Basic defines this subalgebra with
  carrier exactly the integral elements (line 216). No private definition.
- Canonical spectrum map: `let f := Spec.map
  (CommRingCat.ofHom (algebraMap A C))`. Correct direction Spec C -> Spec A.
- C Dedekind in the node's dimension-exactly-one convention:
  `IsDedekindDomain C ∧ ringKrullDim C = 1`. Repaired. Mathlib's class extends
  `IsDomain`, Noetherianity, `DimensionLEOne`, and integral closedness in the
  fraction field (DedekindDomain/Basic.lean:118,145). The normal-domain dependency
  records `IsDomain` plus `IsIntegrallyClosed`, which is exactly this fraction-field
  closedness, not the more general local normal-ring notion. The first worker
  used only `IsDedekindDomain C`; its dimension-at-most-one convention omitted
  the node's explicit dimension-one clause. The added equality restores it.
- Surjectivity: `Function.Surjective f.base`. Correct on all spectrum points.
- Finite fibres: `∀ y : Spec (CommRingCat.of A), Finite (f ⁻¹' {y})`.
  Correct set-theoretic fibre, with no choice of ordering or cardinal bound.
- Finite induced residue extensions: `∀ x : Spec (CommRingCat.of C),
  (f.residueFieldMap x).hom.Finite`. Correct canonical map k(f(x)) -> k(x):
  Scheme.Hom.residueFieldMap is induced by the stalk map (ResidueField.lean:123),
  and RingHom.Finite means a finitely generated module via that exact ring map
  (Finiteness/Defs.lean:170). For fields this is finite extension degree.

Edge cases: zero rings and empty spectra cannot satisfy the domain and dimension
 hypotheses; fields A are excluded by dimension exactly one. The trivial field
 extension L = K is allowed. Generic and closed points are both quantified over,
 including the generic finite extension L/K. No index set or n occurs; finite
 fibre subtypes can be empty as a predicate, with nonemptiness separately supplied
 by surjectivity. Arbitrary characteristic, inseparable extensions, and nonnormal
 Noetherian base domains are included. I separated the fraction-field universe
 v from the spectrum universe u; A and L live in an arbitrary common ambient
 universe because Mathlib's scheme category fixes that ambient universe. This
 imposes no cardinal bound, and smaller carriers can be transported to the common
 universe. All universe names and all variables are explicitly bound.

Independent searches with different wording:

- `msearch.py leanfinder "normalization of a one dimensional noetherian domain
  finite extension finite fibers residue fields"`: returned quasi-finite residue
  field lemmas and finite normal-closure results. Their hypotheses require
  quasi-finiteness or finite module structure/normality already, so none is 09IG.
- `msearch.py loogle "IsDedekindDomain, integralClosure"`: returned
  `integralClosure.isDedekindDomain` and its fraction-ring specialization.
  I opened DedekindDomain/IntegralClosure.lean, including the section variable
  `[Algebra.IsSeparable K L]` and the theorem's `[IsDedekindDomain A]` assumption;
  both are extra assumptions here, and neither gives the spectrum clauses.
- `msearch.py leansearch "integral closure of noetherian domain dimension one
  spectrum surjective finite fibres"`: unavailable (Internal Server Error);
  no mathematical verdict is inferred from that service failure.
- `rg` of Mathlib RingTheory for `akizuki`, Dedekind with fibre/fiber,
  `integralClosure.*surject`, and the proposed full declaration name; and `rg`
  of the upstream WeilConjectures tree and this repository's lean/Sheaf for the
  same concepts: no duplicate theorem. The upstream Dominating module mentions
  Krull--Akizuki in its description but does not state this result.

Other repairs: the former proof docstring merely named ingredients and even had
 a stranded "the" line. It now follows all four DAG proof steps, naming each
 dependency, describing localization at maximal ideals and preservation of residue
 fields, and handling the generic fibre with incomparability. The module and
 theorem retain their source and blueprint tags. There is exactly one theorem,
 whose proof remains `sorry`; there are no definitions containing holes and no
 proofs added. The node's lean.statement is the exact multiline signature copied
 from the edited file. The corrected module compiled on the server in 1.8 seconds,
 exit code 0, with no warnings.
