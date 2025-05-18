import Game.Levels.W01.SpaceWorld

-- Here's what we'll put on the title screen
Title "Topology Game"
Introduction
"
Welcome to the Topology Game! During this game, you will
learn an introduction to the Lean theorem prover in the context
of introductory topology.
"

Info "
This game is a work in progress.

(c) 2025 Steven Clontz and Jim Fowler

<https://github.com/kisonecat/topology-game>
"

/-! Information to be displayed on the servers landing page. -/
Languages "English"
CaptionShort "Topology Game"
CaptionLong "An introduction to Lean using topology."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
