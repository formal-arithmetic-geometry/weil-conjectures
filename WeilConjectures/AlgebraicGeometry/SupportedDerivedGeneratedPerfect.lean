/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.QuasiSeparated

/-! # Building supported derived objects from a perfect complex

Source: Stacks Project, proof of Lemma 48.4.3(3) (Tag 0E4G), using Lemmas 36.15.4
(Tag 0A9A) and 13.37.3 (Tag 09SN)
(blueprint: lem-sc-supported-derived-generated-perfect).

Coproducts are specified by colimiting cofans, so the statement does not require a chosen
coproduct instance. Distinguished triangles are taken in the ambient derived category;
the sequence objects lie in its full quasi-coherent subcategory.
-/
