## Worker report

The module `Sheaf.AlgebraicGeometry.GeometricCurveLevelFaithfulness` states
`AlgebraicGeometry.geometric_curve_level_faithfulness`. Its only theorem has proof `sorry`;
no definition or proof is introduced. The node's natural-language statement is unchanged.

Hypothesis and conclusion correspondence:

- The algebraically closed field is `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`.
- The curve over Ω is `{C : Scheme.{u}} (f : C ⟶ Spec (.of Ω))` with
  `[IsConnectedCurve f]`. That recorded class extends `IsCurve f`, hence includes separatedness,
  finite type, connectedness, nonemptiness and dimension exactly one. No geometric
  connectedness or integrality hypothesis is added.
- Smoothness is `[Smooth f]`. Projectivity in the blueprint's finite-projective-space
  convention is `[IsHProjective f]`, rather than a stronger embedding datum.
- Genus at least two is `hgenus : 2 ≤ f.genus`. The recorded genus declaration uses the
  equivalent dimension of global relative differentials; on these smooth proper connected
  curves it equals the dimension of H¹(O), as its docstring records. Projectivity implies
  properness, so this is exactly the node's genus.
- The level is `(ℓ : ℕ) (hprime : ℓ.Prime) (hlevel : 3 ≤ ℓ)`. The characteristic condition
  is `hchar : (ℓ : Ω) ≠ 0`: for a prime ℓ in a field this is equivalent to ℓ differing from
  the characteristic. It includes characteristic zero.
- The Ω-automorphism is `(a : C ≅ C) (hover : a.hom ≫ f = f)`. An isomorphism whose
  forward map is over Ω also has its inverse over Ω, so this specifies exactly an
  automorphism over the field.
- The coefficient sheaf is `C.constantZMod ℓ`, the existing abbreviation for
  `(constantSheaf C.smallEtaleTopology AddCommGrpCat.{u+1}).obj
  (AddCommGrpCat.of (ULift.{u+1} (ZMod ℓ)))`. The lift only puts the finite abelian group
  in the coefficient universe of the small étale site.
- `hacts` quantifies over every `x : Sheaf.H (C.constantZMod ℓ) 1`. First
  `Etale.cohomologyMap a.hom (C.constantZMod ℓ) 1` pulls the class back to cohomology of
  the pulled-back sheaf. Then `Sheaf.H.map` of
  `(Scheme.upperStarConstantSheafIso AddCommGrpCat.{u+1} a.hom).hom.app ...`
  returns to the original constant sheaf. Equality to `x` is precisely the identity action.
  The coefficient isomorphism is canonical, with no arbitrary comparison or action supplied
  as a hypothesis. `Sheaf.H` is the existing Ext presentation of étale sheaf cohomology;
  the cohomology dependency record explicitly permits this source-library spelling,
  equivalent to its `Etale.cohomology` on the degree-zero sheaf.
- The conclusion is `a = Iso.refl C`, equality of the curve automorphism to the identity.

Statement dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs; `IsAlgClosed`, Mathlib.FieldTheory.IsAlgClosed.Basic
  (the algebraic-closure node's match explicitly includes this predicate).
- `AlgebraicGeometry.IsCurve`, `IsConnectedCurve`, `Scheme.Hom.genus`, all in
  WeilConjectures.AlgebraicGeometry.Curve.
- `AlgebraicGeometry.IsHProjective`, WeilConjectures.AlgebraicGeometry.Morphisms.Projective.
- `AlgebraicGeometry.Etale.cohomology` and `rightDerivedGlobalSections`,
  WeilConjectures.SixFunctors.Etale.Derived.LowerShriek; the statement uses the permitted
  `CategoryTheory.Sheaf.H` presentation as explained above and imports this dependency.
- `CategoryTheory.constantSheaf`, Mathlib.CategoryTheory.Sites.ConstantSheaf, through the
  existing `AlgebraicGeometry.Scheme.constantZMod` abbreviation in
  WeilConjectures.AlgebraicGeometry.Sites.Kummer.
- The actual action uses `AlgebraicGeometry.Etale.cohomologyMap` in
  WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance and
  `AlgebraicGeometry.Scheme.upperStarConstantSheafIso` in
  WeilConjectures.ConstructibleSheaf.Defs. Both full signatures and docstrings were read.

All recorded proof-dependency modules are imported without `public`; the Picard main node's
closed upstream audit gives both Picard.Scheme and Picard.Jacobian, which are imported.
Three proof dependencies currently have no recorded or audited declaration and thus no module
to import: `lem-sfb-curve-polarized-jacobian-faithfulness`,
`lem-sfb-polarized-abelian-odd-level-rigidity`, and `det-cor-jacobian-torsion-pic`.
None is needed to type this statement. The five-step proof docstring names them at exactly
the corresponding steps of the DAG proof. No statement dependency is missing or repaired.

Edge cases checked: the empty scheme and zero-dimensional schemes are excluded by the node's
connected-curve condition itself. Genus zero and one are excluded by `hgenus` (translations
in genus one illustrate why this matters). Level two is excluded by `hlevel`; the
hyperelliptic involution illustrates the necessity of odd level. Characteristic two is
allowed for odd ℓ; characteristic ℓ is excluded by `hchar`; characteristic zero is allowed.
The identity automorphism has the expected canonical coefficient comparison. All universe
variables and binders are explicit, with the established coefficient universe u+1.

Searches for an existing statement (all through msearch.py, group Q51, this item):

- LeanFinder: "An automorphism of a smooth projective connected curve of genus at least two
  acting trivially on first etale cohomology modulo an odd prime is the identity".
  Eight unrelated hits, including group-cohomology Hilbert 90, Galois category automorphisms,
  elliptic-curve isomorphisms and cyclotomic-character identities; no matching theorem.
- Loogle: "AlgebraicGeometry.Etale.cohomologyMap, AlgebraicGeometry.IsCurve".
  No hits (the service does not index the project-specific cohomologyMap).
- LeanSearch: "An automorphism of a curve of genus at least two acting trivially on first
  cohomology modulo an odd prime is the identity". Eight unrelated group-cohomology,
  elliptic-curve and identity-action hits; no matching theorem.
- Mathlib grep: `faithful.*[Cc]urve|[Cc]urve.*faithful|[Ll]evel.*[Aa]ut|[Aa]ut.*[Ll]evel`.
  Two irrelevant hits (Data.Rel and Galois.Prorepresentability).
- Direct rg of WeilConjectures and Sheaf for curve/faithful, level/aut, constantZMod/aut and
  candidate declaration names: no existing geometric rigidity theorem. The sole mention of
  this node in SmoothCurveAbelianLevelRigidification is in its downstream proof docstring,
  not a declaration of the result. Direct grep for the node id in WeilConjectures found none.
  Candidate-name search of dag/lean_names_upstream.json found none.

The primary source https://arxiv.org/pdf/alg-geom/9501003 was opened and Sections 1.1(1) and
2.3.3 read: genus is at least two throughout; the abelian level is an isomorphism to R¹f_*
of Z/m, m is invertible on the base, and m at least three gives a fine moduli scheme.
This agrees with the isolated geometric-stabilizer assertion; no correction or dispute.

Validation: scompile.py compiled the sandbox module and its actual library module name
cleanly (5.8 and 6.0 seconds respectively), with no errors or warnings.

## Second reading by Q51

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
