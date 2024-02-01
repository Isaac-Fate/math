using Plots
using LaTeXStrings

function plot_curve!(
    plotobj::Plots.Plot,
    z,
    a::Real,
    b::Real;
    step_size::Real=0.01,
    arrow_points::Union{Array{T},Nothing}=nothing,
    δ::Real=1e-3,
    color::Union{RGB,Symbol}=:black,
    linewidth::Int=1,
    linestyle::Symbol=:solid,
    label::Union{AbstractString,Nothing}=nothing,
)::Plots.Plot where {T<:Real}
    # Create a range of values for t
    t = a:step_size:b

    # Parse the color
    if typeof(color) == Symbol
        color = Colors.parse(Colorant, color)
    end

    # Plot the curve
    plot!(
        plotobj,
        real(z.(t)),
        imag(z.(t)),
        color=color,
        xlabel=L"\mathrm{Re}(z)",
        ylabel=L"\mathrm{Im}(z)",
        linewidth=linewidth,
        linestyle=linestyle,
        label=label,
    )

    # Return the plot object if no arrow points are given
    if isnothing(arrow_points)
        return plotobj
    end

    # Plot the arrows in the direction of the curve
    for t in arrow_points
        quiver!(
            [real(z(t))],
            [imag(z(t))],
            quiver=(
                [real(z(t + δ) - z(t))],
                [imag(z(t + δ) - z(t))],
            ),
            color=color,
            linewidth=linewidth,
        )
    end

    return plotobj
end

function plot_curve!(
    z,
    a::Real,
    b::Real;
    step_size::Real=0.01,
    arrow_points::Union{Array{T},Nothing}=nothing,
    δ::Real=1e-3,
    color::Union{RGB,Symbol}=:black,
    linewidth::Int=1,
    linestyle::Symbol=:solid,
    label::Union{AbstractString,Nothing}=nothing,
)::Plots.Plot where {T<:Real}
    # Get the current plot object
    plotobj = current()

    # Plot in the current plot object
    plot_curve!(
        plotobj,
        z,
        a,
        b,
        step_size=step_size,
        arrow_points=arrow_points,
        δ=δ,
        color=color,
        linewidth=linewidth,
        linestyle=linestyle,
        label=label,
    )
end

function plot_curve(
    z,
    a::Real,
    b::Real;
    step_size::Real=0.01,
    arrow_points::Union{Array{T},Nothing}=nothing,
    δ::Real=1e-3,
    color::Union{RGB,Symbol}=:black,
    linewidth::Int=1,
    linestyle::Symbol=:solid,
    label::Union{AbstractString,Nothing}=nothing,
)::Plots.Plot where {T<:Real}
    # Create a new plot object
    plotobj = plot()

    # Plot in the current plot object
    plot_curve!(
        plotobj,
        z,
        a,
        b,
        step_size=step_size,
        arrow_points=arrow_points,
        δ=δ,
        color=color,
        linewidth=linewidth,
        linestyle=linestyle,
        label=label,
    )
end
