module

public import Mathlib.CategoryTheory.Category.Basic

@[expose] public section
universe u v
open CategoryTheory
namespace AlgebraicGeometry.Etale

private lemma chart_comp_assoc_eq {K : Type u} [Category.{v} K]
    {A B C D E F G : K}
    (p : A ⟶ B) (a : B ⟶ C) (b : C ⟶ D) (c : D ⟶ E)
    (d : E ⟶ F) (e : F ⟶ G) (r : B ⟶ G)
    (h : a ≫ b ≫ c ≫ d ≫ e = r) :
    p ≫ a ≫ b ≫ c ≫ d ≫ e = p ≫ r := by
  simpa only [Category.assoc] using congrArg (p ≫ ·) h

lemma chart_comp_assoc_eq_left {K : Type u} [Category.{v} K]
    {A B C D E F G : K}
    (p : A ⟶ B) (a : B ⟶ C) (b : C ⟶ D) (c : D ⟶ E)
    (d : E ⟶ F) (e : F ⟶ G) (r : B ⟶ G)
    (h : a ≫ b ≫ c ≫ d ≫ e = r) :
    (((((p ≫ a) ≫ b) ≫ c) ≫ d) ≫ e) = p ≫ r := by
  simpa only [Category.assoc] using congrArg (p ≫ ·) h

lemma chart_comp_assoc_eq_target {K : Type u} [Category.{v} K]
    {A B C D E F G : K}
    (p : A ⟶ B) (a : B ⟶ C) (b : C ⟶ D) (c : D ⟶ E)
    (d : E ⟶ F) (e : F ⟶ G) (r : B ⟶ G)
    (h : a ≫ b ≫ c ≫ d ≫ e = r) :
    ((p ≫ a) ≫ b ≫ c ≫ d) ≫ e = p ≫ r := by
  simpa only [Category.assoc] using congrArg (p ≫ ·) h

lemma chart_comp_assoc_eq_targetB {K : Type u} [Category.{v} K]
    {A B C D E F G : K}
    (p : A ⟶ B) (a : B ⟶ C) (b : C ⟶ D) (c : D ⟶ E)
    (d : E ⟶ F) (e : F ⟶ G) (r : B ⟶ G)
    (h : a ≫ b ≫ c ≫ d ≫ e = r) :
    ((p ≫ a) ≫ (b ≫ c ≫ d)) ≫ e = p ≫ r := by
  simpa only [Category.assoc] using congrArg (p ≫ ·) h

lemma chart_comp_assoc_eq_targetC {K : Type u} [Category.{v} K]
    {A B C D E F G : K}
    (p : A ⟶ B) (a : B ⟶ C) (b : C ⟶ D) (c : D ⟶ E)
    (d : E ⟶ F) (e : F ⟶ G) (r : B ⟶ G)
    (h : a ≫ b ≫ c ≫ d ≫ e = r) :
    ((p ≫ a) ≫ b ≫ (c ≫ d)) ≫ e = p ≫ r := by
  simpa only [Category.assoc] using congrArg (p ≫ ·) h

lemma chart_comp_assoc_eq_targetD {K : Type u} [Category.{v} K]
    {A B C D E F G : K}
    (p : A ⟶ B) (a : B ⟶ C) (b : C ⟶ D) (c : D ⟶ E)
    (d : E ⟶ F) (e : F ⟶ G) (r : B ⟶ G)
    (h : a ≫ b ≫ c ≫ d ≫ e = r) :
    (((p ≫ a) ≫ b) ≫ c) ≫ (d ≫ e) = p ≫ r := by
  simpa only [Category.assoc] using congrArg (p ≫ ·) h

lemma chart_comp_assoc_eq_targetE {K : Type u} [Category.{v} K]
    {A B C D E F G : K}
    (p : A ⟶ B) (a : B ⟶ C) (b : C ⟶ D) (c : D ⟶ E)
    (d : E ⟶ F) (e : F ⟶ G) (r : B ⟶ G)
    (h : a ≫ b ≫ c ≫ d ≫ e = r) :
    (((p ≫ a) ≫ b) ≫ (c ≫ d)) ≫ e = p ≫ r := by
  simpa only [Category.assoc] using congrArg (p ≫ ·) h

lemma chart_comp_assoc_eq_targetF {K : Type u} [Category.{v} K]
    {A B C D E F G : K}
    (p : A ⟶ B) (a : B ⟶ C) (b : C ⟶ D) (c : D ⟶ E)
    (d : E ⟶ F) (e : F ⟶ G) (r : B ⟶ G)
    (h : a ≫ b ≫ c ≫ d ≫ e = r) :
    p ≫ (a ≫ b ≫ c ≫ d) ≫ e = p ≫ r := by
  simpa only [Category.assoc] using congrArg (p ≫ ·) h

lemma chart_comp_assoc_eq_targetG {K : Type u} [Category.{v} K]
    {A B C D E F G : K}
    (p : A ⟶ B) (a : B ⟶ C) (b : C ⟶ D) (c : D ⟶ E)
    (d : E ⟶ F) (e : F ⟶ G) (r : B ⟶ G)
    (h : a ≫ b ≫ c ≫ d ≫ e = r) :
    ((p ≫ a) ≫ (b ≫ (c ≫ d))) ≫ e = p ≫ r := by
  simpa only [Category.assoc] using congrArg (p ≫ ·) h

lemma chart_comp_assoc_reassociate {K : Type u} [Category.{v} K]
    {A B C D E F G : K}
    (p : A ⟶ B) (a : B ⟶ C) (b : C ⟶ D) (c : D ⟶ E)
    (d : E ⟶ F) (e : F ⟶ G) (r : B ⟶ G)
    (h : p ≫ a ≫ b ≫ c ≫ d ≫ e = p ≫ r) :
    ((p ≫ a) ≫ b ≫ c ≫ d) ≫ e = p ≫ r := by
  simpa only [Category.assoc] using h

lemma chart_comp_assoc_reassociateB {K : Type u} [Category.{v} K]
    {A B C D E F G : K}
    (p : A ⟶ B) (a : B ⟶ C) (b : C ⟶ D) (c : D ⟶ E)
    (d : E ⟶ F) (e : F ⟶ G) (r : B ⟶ G)
    (h : p ≫ a ≫ b ≫ c ≫ d ≫ e = p ≫ r) :
    ((p ≫ a) ≫ (b ≫ c ≫ d)) ≫ e = p ≫ r := by
  simpa only [Category.assoc] using h

lemma chart_comp_assoc_reassociateC {K : Type u} [Category.{v} K]
    {A B C D E F G : K}
    (p : A ⟶ B) (a : B ⟶ C) (b : C ⟶ D) (c : D ⟶ E)
    (d : E ⟶ F) (e : F ⟶ G) (r : B ⟶ G)
    (h : p ≫ a ≫ b ≫ c ≫ d ≫ e = p ≫ r) :
    ((p ≫ a) ≫ b ≫ (c ≫ d)) ≫ e = p ≫ r := by
  simpa only [Category.assoc] using h

lemma chart_comp_assoc_reassociateD {K : Type u} [Category.{v} K]
    {A B C D E F G : K}
    (p : A ⟶ B) (a : B ⟶ C) (b : C ⟶ D) (c : D ⟶ E)
    (d : E ⟶ F) (e : F ⟶ G) (r : B ⟶ G)
    (h : p ≫ a ≫ b ≫ c ≫ d ≫ e = p ≫ r) :
    (((p ≫ a) ≫ b) ≫ (c ≫ d)) ≫ e = p ≫ r := by
  simpa only [Category.assoc] using h

lemma chart_comp_assoc_reassociateOuter {K : Type u} [Category.{v} K]
    {A B C D E F G : K}
    (p : A ⟶ B) (a : B ⟶ C) (b : C ⟶ D) (c : D ⟶ E)
    (d : E ⟶ F) (e : F ⟶ G) (r : B ⟶ G)
    (h : p ≫ a ≫ b ≫ c ≫ d ≫ e = p ≫ r) :
    (p ≫ (a ≫ b ≫ c ≫ d)) ≫ e = p ≫ r := by
  simpa only [Category.assoc] using h

end AlgebraicGeometry.Etale
